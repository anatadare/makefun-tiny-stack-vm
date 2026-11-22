// Tiny stack VM: 32-bit wrapping ints, 256-value data stack, 64-entry call
// stack, 256 words of memory, ten traps. Runs every instance in the input
// dir and writes stdout.bin + exit.txt per instance. Node 22, no deps.
import { existsSync as ex, mkdirSync as mk, readdirSync as rd, readFileSync as rf, writeFileSync as wf } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input', O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
// Opcode table, built once: which bytes are real opcodes and their immediate length.
const OK = new Uint8Array(256), IMM = new Uint8Array(256);
for (const o of [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 48, 49, 50, 51, 52, 64, 65, 80, 81, 82, 83]) OK[o] = 1;
IMM[1] = 1; IMM[2] = 4; IMM[48] = IMM[49] = IMM[50] = IMM[51] = 2;
function run(p: Buffer, inp: Buffer): [Buffer, number] {
  const n = p.length, st = new Int32Array(256), cs = new Int32Array(64), mm = new Int32Array(256), out = Buffer.allocUnsafe(65536);
  let sp = 0, cp = 0, ip = 0, pc = 0, steps = 0, ol = 0;
  const fin = (e: number): [Buffer, number] => [out.subarray(0, ol), e];
  for (;;) {
    if (steps === 1e6) return fin(10);
    if (pc < 0 || pc >= n) return fin(9);
    const op = p[pc];
    if (!OK[op]) return fin(5);
    const imm = IMM[op];
    if (pc + imm >= n) return fin(9);
    steps++;
    const nx = pc + 1 + imm;
    pc = nx;
    switch (op) {
      case 0: return fin(0);
      case 1:
        if (sp >= 256) return fin(3);
        st[sp++] = (p[nx - 1] << 24) >> 24;
        break;
      case 2:
        if (sp >= 256) return fin(3);
        st[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24);
        break;
      case 3:
        if (sp < 1) return fin(2);
        sp--;
        break;
      case 4:
        if (sp < 1) return fin(2);
        if (sp >= 256) return fin(3);
        st[sp] = st[sp - 1]; sp++;
        break;
      case 5:
        if (sp < 2) return fin(2);
        { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; }
        break;
      case 6:
        if (sp < 2) return fin(2);
        if (sp >= 256) return fin(3);
        st[sp] = st[sp - 2]; sp++;
        break;
      case 7: {
        if (sp < 3) return fin(2);
        const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a;
        break;
      }
      case 23:
        if (sp < 1) return fin(2);
        st[sp - 1] = -st[sp - 1] | 0;
        break;
      case 27:
        if (sp < 1) return fin(2);
        st[sp - 1] = ~st[sp - 1];
        break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30: case 32:
      case 33: case 34: {
        if (sp < 2) return fin(2);
        const b = st[sp - 1], a = st[sp - 2];
        let r: number;
        switch (op) {
          case 16: r = (a + b) | 0; break;
          case 17: r = (a - b) | 0; break;
          case 18: r = Math.imul(a, b); break;
          case 19:
            if (b === 0) return fin(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 20:
            if (b === 0) return fin(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 21:
            if (b === 0) return fin(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 22:
            if (b === 0) return fin(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 24: r = a & b; break;
          case 25: r = a | b; break;
          case 26: r = a ^ b; break;
          case 28: r = a << (b & 31); break;
          case 29: r = a >> (b & 31); break;
          case 30: r = (a >>> (b & 31)) | 0; break;
          case 32: r = a === b ? 1 : 0; break;
          case 33: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        }
        sp -= 2; st[sp++] = r;
        break;
      }
      case 48: case 49: case 50: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 48) {
          if (sp < 1) return fin(2);
          const v = st[--sp];
          take = op === 49 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 51:
        if (cp === 64) return fin(7);
        cs[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52:
        if (cp === 0) return fin(8);
        pc = cs[--cp];
        break;
      case 64: {
        if (sp < 1) return fin(2);
        const a = st[sp - 1];
        if (a < 0 || a >= 256) return fin(6);
        st[sp - 1] = mm[a];
        break;
      }
      case 65: {
        if (sp < 2) return fin(2);
        const a = st[sp - 1], v = st[sp - 2];
        if (a < 0 || a >= 256) return fin(6);
        mm[a] = v; sp -= 2;
        break;
      }
      case 80: {
        if (sp < 1) return fin(2);
        const s = String(st[sp - 1]);
        if (ol + s.length > 65536) return fin(11);
        out.write(s, ol, 'ascii'); ol += s.length; sp--;
        break;
      }
      case 81: {
        if (sp < 1) return fin(2);
        if (ol + 1 > 65536) return fin(11);
        out[ol++] = st[--sp] & 255;
        break;
      }
      case 82:
        if (sp >= 256) return fin(3);
        st[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      default:
        if (sp < 1) return fin(2);
        return fin(st[--sp] & 255);
    }
  }
}
for (const e of rd(I, { withFileTypes: true }).sort((a, b) => (a.name < b.name ? -1 : 1))) {
  if (!e.isDirectory()) continue;
  const prog = rf(join(I, e.name, 'program.bin'));
  const ip = join(I, e.name, 'input.bin');
  const [o, x] = run(prog, ex(ip) ? rf(ip) : Buffer.alloc(0));
  mk(join(O, e.name), { recursive: true });
  wf(join(O, e.name, 'stdout.bin'), o);
  wf(join(O, e.name, 'exit.txt'), `${x}\n`);
}
