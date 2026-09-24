#!/usr/bin/env python3
"""Numerical instance of Lemma 2.25 of Jones (1982), necessity direction.

Takes R = 63 (so that 2^6 | C(2R, R) by Kummer: 63 has six binary ones),
N = 8, b = 8, and constructs the witnesses exactly as in the necessity proof:
w with bw = 2^(2R+1), U = N^2 w, rho = (U+1)^(2R)/U^R, Y = [rho], s = Y/N^2,
M = RY, A = M(U+1), B' = 2R+1, C = psi_A(B'), P = 2M^2 U, K = psi_P(R+1),
h from K = R+1+h(P-1), W = bw, V = 2, phi from C = B'+W+phi.  Then every one
of (B1)-(B14) (with (B8')) is checked with exact integer arithmetic.  The
Pell numbers involved have about a million bits.  Standard library only.
"""
from __future__ import annotations
import json
from math import comb
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / "round4_1982_lemma225_results.json"

def need(cond, msg):
    if not cond:
        raise AssertionError(msg)

def psi(A, n):
    """psi_A(n): second Pell coordinate, psi(0)=0, psi(1)=1, psi(n+2)=2A psi(n+1)-psi(n)."""
    x0, x1 = 0, 1
    if n == 0:
        return 0
    for _ in range(n - 1):
        x0, x1 = x1, 2*A*x1 - x0
    return x1

def issquare(n):
    if n < 0:
        return False
    r = int(n**0.5) if n < (1 << 52) else None
    from math import isqrt
    r = isqrt(n)
    return r*r == n

R, N, b = 63, 8, 8
need(R >= 8 and N >= 8 and R >= b and N >= b > 0, "initial conditions")
need(comb(2*R, R) % (N*N) == 0, "N^2 | C(2R,R) must hold for the necessity instance")
w = 2**(2*R + 1) // b; need(b*w == 2**(2*R + 1), "bw = 2^(2R+1)")
U = N*N*w                       # (B9)
V = 2                            # (B12)
W = b*w                          # (B11)
rho_num, rho_den = (U + 1)**(2*R), U**R
Y = rho_num // rho_den           # Y = [rho]
need(Y % (N*N) == 0, "N^2 | Y")
s = Y // (N*N)                   # (B10)
M = R*Y                          # (B5)
A = M*(U + 1)                    # (B6)
Bp = 2*R + 1                     # (B7)
C = psi(A, Bp)                   # (B14)
phi = C - Bp - W                 # (B8')
need(phi > 0, "(B8') phi positive")
P = 2*M*M*U                      # (B1)
K = psi(P, R + 1)
need(issquare((P*P - 1)*K*K + 1), "(B2)")
need((K - R - 1) % (P - 1) == 0 and (K - R - 1)//(P - 1) > 0, "(B4)")
h = (K - R - 1)//(P - 1)
# (B3): (C/K - Y)^2 < 1/4  <=>  4 (C - K Y)^2 < K^2
need(4*(C - K*Y)**2 < K*K, "(B3)")
# the proof's sharper statement |C/K - Y| < 1/4  <=>  16 (C-KY)^2 < K^2
need(16*(C - K*Y)**2 < K*K, "(B3) sharper form from the necessity proof")
# (B13): (V^2-1) W C == V (W^2-1)  (mod 2AV - V^2 - 1)
mod = 2*A*V - V*V - 1
need(((V*V - 1)*W*C - V*(W*W - 1)) % mod == 0, "(B13)")
# the chi-form used in Theorem 3: D == W + C(A-V) (mod 2AV-V^2-1), D = chi_A(B')
def chi(A, n):
    x0, x1 = 1, A
    if n == 0:
        return 1
    for _ in range(n - 1):
        x0, x1 = x1, 2*A*x1 - x0
    return x1
D = chi(A, Bp)
need(D*D == (A*A - 1)*C*C + 1, "Pell identity for (C, D)")
need((D - (W + C*(A - V))) % mod == 0, "chi-form congruence")
# Lemma 2.24 statement used in the proof: [rho] == C(2R,R) (mod U)
need((Y - comb(2*R, R)) % U == 0, "[rho] == C(2R,R) mod U")
report = {"status": "PASS", "R": R, "N": N, "b": b, "bits": {"U": U.bit_length(), "Y": Y.bit_length(),
          "A": A.bit_length(), "C": C.bit_length(), "P": P.bit_length(), "K": K.bit_length()},
          "checked": "(B1)-(B14) with (B8'), sharper (B3), chi-form congruence, [rho] mod U"}
OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps(report, indent=2))
