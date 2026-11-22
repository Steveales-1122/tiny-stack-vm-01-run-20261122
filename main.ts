// Tiny stack VM: fast, exact interpreter of make.fun's tiny stack ISA v1.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// T[op] = pops | pushes<<4 | imm<<8, -1 = unknown opcode.
const T = new Int16Array(256).fill(-1);
for (const [op, pops, pushes, imm] of [
  [0x00, 0, 0, 0], [0x01, 0, 1, 1], [0x02, 0, 1, 4], [0x03, 1, 0, 0],
  [0x04, 1, 2, 0], [0x05, 2, 2, 0], [0x06, 2, 3, 0], [0x07, 3, 3, 0],
  [0x10, 2, 1, 0], [0x11, 2, 1, 0], [0x12, 2, 1, 0], [0x13, 2, 1, 0],
  [0x14, 2, 1, 0], [0x15, 2, 1, 0], [0x16, 2, 1, 0], [0x17, 1, 1, 0],
  [0x18, 2, 1, 0], [0x19, 2, 1, 0], [0x1a, 2, 1, 0], [0x1b, 1, 1, 0],
  [0x1c, 2, 1, 0], [0x1d, 2, 1, 0], [0x1e, 2, 1, 0], [0x20, 2, 1, 0],
  [0x21, 2, 1, 0], [0x22, 2, 1, 0], [0x30, 0, 0, 2], [0x31, 1, 0, 2],
  [0x32, 1, 0, 2], [0x33, 0, 0, 2], [0x34, 0, 0, 0], [0x40, 1, 1, 0],
  [0x41, 2, 0, 0], [0x50, 1, 0, 0], [0x51, 1, 0, 0], [0x52, 0, 1, 0],
  [0x53, 1, 0, 0],
]) T[op] = pops | (pushes << 4) | (imm << 8);

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, inPos = 0, pc = 0, steps = 0;
  for (;;) {
    if (steps === 1000000) return { out: out.subarray(0, olen), code: 10 };
    if (pc < 0 || pc >= n) return { out: out.subarray(0, olen), code: 9 };
    const op = p[pc];
    const t = T[op];
    if (t < 0) return { out: out.subarray(0, olen), code: 5 };
    if (pc + (t >> 8) >= n) return { out: out.subarray(0, olen), code: 9 };
    steps++;
    const next = pc + 1 + (t >> 8);
    const pops = t & 15, pushes = (t >> 4) & 15;
    if (sp < pops) return { out: out.subarray(0, olen), code: 2 };
    if (sp - pops + pushes > 256) return { out: out.subarray(0, olen), code: 3 };
    pc = next;
    switch (op) {
      case 0x00: return { out: out.subarray(0, olen), code: 0 };
      case 0x01: D[sp++] = (p[next - 1] << 24) >> 24; break;
      case 0x02:
        D[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24);
        break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const v = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = v; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const v = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = v; break; }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return { out: out.subarray(0, olen), code: 4 };
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return { out: out.subarray(0, olen), code: 4 };
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return { out: out.subarray(0, olen), code: 4 };
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return { out: out.subarray(0, olen), code: 4 };
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2; D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (csp === 64) return { out: out.subarray(0, olen), code: 7 };
        C[csp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return { out: out.subarray(0, olen), code: 8 };
        pc = C[--csp];
        break;
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr >= 256) return { out: out.subarray(0, olen), code: 6 };
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = D[sp - 1], v = D[sp - 2];
        if (addr < 0 || addr >= 256) return { out: out.subarray(0, olen), code: 6 };
        sp -= 2; M[addr] = v;
        break;
      }
      case 0x50: {
        const v = D[sp - 1];
        const neg = v < 0;
        let u = neg ? -v : v;
        let len = neg ? 1 : 0, q = u;
        do { len++; q = (q / 10) | 0; } while (q > 0);
        if (olen + len > 65536) return { out: out.subarray(0, olen), code: 11 };
        sp--;
        let i = olen + len;
        q = u;
        do { out[--i] = 48 + (q % 10); q = (q / 10) | 0; } while (q > 0);
        if (neg) out[--i] = 45;
        olen += len;
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return { out: out.subarray(0, olen), code: 11 };
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = inPos < inp.length ? inp[inPos++] : -1; break;
      case 0x53: return { out: out.subarray(0, olen), code: D[--sp] & 255 };
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
