#!/usr/bin/env python3
"""Independent verifier: decimal streaming only, no full A or modular inverse.

This intentionally does not import tetration_tools or verify.py.  The proof in
article.pdf explains why the checked residues imply the tower identities.
"""
from pathlib import Path


def check(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit('FAIL: ' + message)


def main() -> None:
    digits = (Path(__file__).resolve().parent/'counterexample.txt').read_text('ascii').strip()
    check(len(digits) == 2544, 'decimal length')
    check(digits[0] == '7', 'leading digit')
    check(all('0' <= x <= '9' for x in digits), 'decimal characters')
    # Construct the moduli by multiplication, rather than inversion or CRT.
    p2, p5 = 1, 1
    for _ in range(2548):
        p2 *= 2
    for _ in range(2547):
        p5 *= 5
    mod2, mod5 = 2*p2, 5*p5
    r2 = r5 = 0
    for ch in digits:
        d = ord(ch) - ord('0')
        r2 = (10*r2+d) % mod2
        r5 = (10*r5+d) % mod5
    check(r2 == p2-1, 'residue modulo 2^2549')
    check(r5 == p5+1, 'residue modulo 5^2548')
    check(digits[-1] == '1', 'allowed final digit')
    # Elementary integer evaluations of the two affine functions.
    s = lambda n: min(1+2548*n, 2547*(n+1))
    check(s(2545) == 6484661, 's_2545')
    check(s(2546) == 6487209, 's_2546')
    check(s(2547) == 6489756, 's_2547')
    check(s(2546)-s(2545) == 2548, 'exceptional gain')
    check(s(2547)-s(2546) == 2547, 'permanent gain')
    print('PASS: independent streaming length, residue, and crossover checks.')
    print('This checks finite arithmetic, not a machine formalization of the LTE proof.')

if __name__ == '__main__':
    main()
