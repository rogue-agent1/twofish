#!/usr/bin/env python3
"""Twofish block cipher — AES finalist, 128-bit blocks, 128/192/256-bit keys.

One file. Zero deps. Does one thing well.

Simplified implementation for educational purposes. Implements the core Twofish
algorithm: key-dependent S-boxes, MDS matrix, PHT, and Feistel rounds.
"""
import struct, sys

# GF(2^8) with primitive polynomial x^8 + x^6 + x^5 + x^3 + 1 = 0x169
def gf_mult(a, b, mod=0x169):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a & 0x100:
            a ^= mod
        b >>= 1
    return result & 0xFF

# Fixed q-permutations (q0 and q1)
Q0_T = [
    [0x8,0x1,0x7,0xD,0x6,0xF,0x3,0x2,0x0,0xB,0x5,0x9,0xE,0xC,0xA,0x4],
    [0xE,0xC,0xB,0x8,0x1,0x2,0x3,0x5,0xF,0x4,0xA,0x6,0x7,0x0,0x9,0xD],
    [0xB,0xA,0x5,0xE,0x6,0xD,0x9,0x0,0xC,0x8,0xF,0x3,0x2,0x4,0x7,0x1],
    [0xD,0x7,0xF,0x4,0x1,0x2,0x6,0xE,0x9,0xB,0x3,0x0,0x8,0x5,0xC,0xA],
]
Q1_T = [
    [0x2,0x8,0xB,0xD,0xF,0x7,0x6,0xE,0x3,0x1,0x9,0x4,0x0,0xA,0xC,0x5],
    [0x1,0xE,0x2,0xB,0x4,0xC,0x3,0x7,0x6,0xD,0xA,0x5,0xF,0x9,0x0,0x8],
    [0x4,0xC,0x7,0x5,0x1,0x6,0x9,0xA,0x0,0xE,0xD,0x8,0x2,0xB,0x3,0xF],
    [0xB,0x9,0x5,0x1,0xC,0x3,0xD,0xE,0x6,0x4,0x7,0xF,0x2,0x0,0x8,0xA],
]

def q_perm(x, t_table):
    a0 = x >> 4
    b0 = x & 0xF
    a1 = a0 ^ b0
    b1 = a0 ^ ((b0 >> 1) | ((b0 & 1) << 3)) ^ ((8 * a0) & 0xF)
    a2 = t_table[0][a1]
    b2 = t_table[1][b1]
    a3 = a2 ^ b2
    b3 = a2 ^ ((b2 >> 1) | ((b2 & 1) << 3)) ^ ((8 * a2) & 0xF)
    a4 = t_table[2][a3]
    b4 = t_table[3][b3]
    return (b4 << 4) | a4

def q0(x): return q_perm(x, Q0_T)
def q1(x): return q_perm(x, Q1_T)

# MDS matrix
MDS = [
    [0x01, 0xEF, 0x5B, 0x5B],
    [0x5B, 0xEF, 0xEF, 0x01],
    [0xEF, 0x5B, 0x01, 0xEF],
    [0xEF, 0x01, 0xEF, 0x5B],
]

def mds_mult(vec):
    result = [0] * 4
    for i in range(4):
        for j in range(4):
            result[i] ^= gf_mult(MDS[i][j], vec[j])
    return result

def h_func(x, key_bytes, k):
    """The h function used in key schedule and round function."""
    y = [(x >> (8 * i)) & 0xFF for i in range(4)]
    if k >= 4:
        y[0] = q1(y[0]) ^ key_bytes[3][0]
        y[1] = q0(y[1]) ^ key_bytes[3][1]
        y[2] = q0(y[2]) ^ key_bytes[3][2]
        y[3] = q1(y[3]) ^ key_bytes[3][3]
    if k >= 3:
        y[0] = q1(y[0]) ^ key_bytes[2][0]
        y[1] = q1(y[1]) ^ key_bytes[2][1]
        y[2] = q0(y[2]) ^ key_bytes[2][2]
        y[3] = q0(y[3]) ^ key_bytes[2][3]
    y[0] = q0(q0(y[0]) ^ key_bytes[1][0]) ^ key_bytes[0][0]
    y[1] = q0(q1(y[1]) ^ key_bytes[1][1]) ^ key_bytes[0][1]
    y[2] = q1(q0(y[2]) ^ key_bytes[1][2]) ^ key_bytes[0][2]
    y[3] = q1(q1(y[3]) ^ key_bytes[1][3]) ^ key_bytes[0][3]
    return mds_mult(y)

class Twofish:
    ROUNDS = 16
    BLOCK_SIZE = 16

    def __init__(self, key):
        klen = len(key)
        assert klen in (16, 24, 32), "Key must be 16, 24, or 32 bytes"
        self.k = klen // 8  # number of 64-bit words
        # Split key into even/odd words
        words = [struct.unpack_from('<I', key, i*4)[0] for i in range(klen//4)]
        me = [words[i*2] for i in range(self.k)]
        mo = [words[i*2+1] for i in range(self.k)]
        # S-box key bytes
        self.s_key = []
        for i in range(self.k):
            self.s_key.append([(key[8*i+j]) for j in range(4)])
        self.s_key.reverse()
        # Subkeys
        self.subkeys = [0] * 40
        rho = 0x01010101
        for i in range(20):
            a = self._h_word(2*i * rho, me)
            b = self._h_word((2*i+1) * rho, mo)
            b = ((b << 8) | (b >> 24)) & 0xFFFFFFFF
            self.subkeys[2*i] = (a + b) & 0xFFFFFFFF
            self.subkeys[2*i+1] = ((a + 2*b) << 9 | (a + 2*b) >> 23) & 0xFFFFFFFF

    def _h_word(self, x, L):
        kb = [[(L[i] >> (8*j)) & 0xFF for j in range(4)] for i in range(self.k)]
        r = h_func(x, kb, self.k)
        return r[0] | (r[1] << 8) | (r[2] << 16) | (r[3] << 24)

    def _g(self, x):
        r = h_func(x, self.s_key, self.k)
        return r[0] | (r[1] << 8) | (r[2] << 16) | (r[3] << 24)

    def encrypt_block(self, block):
        assert len(block) == 16
        r = list(struct.unpack('<4I', block))
        # Input whitening
        for i in range(4):
            r[i] ^= self.subkeys[i]
        for rnd in range(self.ROUNDS):
            t0 = self._g(r[0])
            t1 = self._g(((r[1] << 8) | (r[1] >> 24)) & 0xFFFFFFFF)
            f0 = (t0 + t1 + self.subkeys[8 + 2*rnd]) & 0xFFFFFFFF
            f1 = (t0 + 2*t1 + self.subkeys[9 + 2*rnd]) & 0xFFFFFFFF
            r[2] = ((r[2] ^ f0) >> 1 | (r[2] ^ f0) << 31) & 0xFFFFFFFF
            r[3] = (((r[3] << 1) | (r[3] >> 31)) & 0xFFFFFFFF) ^ f1
            r[0], r[1], r[2], r[3] = r[2], r[3], r[0], r[1]
        r[0], r[1], r[2], r[3] = r[2], r[3], r[0], r[1]
        # Output whitening
        for i in range(4):
            r[i] ^= self.subkeys[4 + i]
        return struct.pack('<4I', *r)

    def decrypt_block(self, block):
        assert len(block) == 16
        r = list(struct.unpack('<4I', block))
        for i in range(4):
            r[i] ^= self.subkeys[4 + i]
        for rnd in range(self.ROUNDS - 1, -1, -1):
            r[0], r[1], r[2], r[3] = r[2], r[3], r[0], r[1]
            t0 = self._g(r[0])
            t1 = self._g(((r[1] << 8) | (r[1] >> 24)) & 0xFFFFFFFF)
            f0 = (t0 + t1 + self.subkeys[8 + 2*rnd]) & 0xFFFFFFFF
            f1 = (t0 + 2*t1 + self.subkeys[9 + 2*rnd]) & 0xFFFFFFFF
            r[2] = (((r[2] << 1) | (r[2] >> 31)) & 0xFFFFFFFF) ^ f0
            r[3] = ((r[3] ^ f1) >> 1 | (r[3] ^ f1) << 31) & 0xFFFFFFFF
        r[0], r[1], r[2], r[3] = r[2], r[3], r[0], r[1]
        for i in range(4):
            r[i] ^= self.subkeys[i]
        return struct.pack('<4I', *r)


def main():
    key = b'\x00' * 16
    pt = b'\x00' * 16
    tf = Twofish(key)
    ct = tf.encrypt_block(pt)
    dt = tf.decrypt_block(ct)
    print(f"Key:        {key.hex()}")
    print(f"Plaintext:  {pt.hex()}")
    print(f"Ciphertext: {ct.hex()}")
    print(f"Decrypted:  {dt.hex()}")
    assert dt == pt, "Decrypt failed!"
    print("✓ Round-trip verified")

if __name__ == "__main__":
    main()
