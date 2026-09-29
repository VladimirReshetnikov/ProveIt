#!/usr/bin/env python3
"""Exact finite checks of the alternative Pell-index family.

The universal parameter argument is in EXPLORATION_RATIO_WITHOUT_SIGNED_INDEX.md.
Large samples check the proved exponent bounds, not materialized Pell coordinates.
"""
from pathlib import Path
import json
import gmpy2 as g


def need(condition, message):
    if not condition:
        raise AssertionError(message)


def pell_pair(A, index):
    A = g.mpz(A)
    D = A*A-1
    chi, psi = g.mpz(1), g.mpz(0)
    for bit in bin(index)[2:]:
        chi2, psi2 = 2*chi*chi-1, 2*chi*psi
        if bit == "1":
            chi, psi = A*chi2+D*psi2, chi2+A*psi2
        else:
            chi, psi = chi2, psi2
    return chi, psi


def exact_case(v):
    p, t = v*v+v+1, v*v+v//2+1
    R = t-1
    U, Y = g.mpz(1) << (2*p), g.mpz(1) << v
    a = Y*(U+1)
    A, Q = a+4, U*Y*Y
    P = 2*Q+1
    d, c = pell_pair(A, p)
    root, k = pell_pair(P, t)
    need(d*d-(A*A-1)*c*c == 1, "exact main Pell norm")
    need(root % 2 == 1 and root > 1, "positive integral triangular root")
    tau = (root-1)//2
    need(tau*(tau+1) == Q*(Q+1)*k*k, "exact first triangular norm")
    eta, zeta = c-Y*k, k-(c-Y*k)
    need(eta > 0 and zeta > 0, "both exact positive interval gaps")
    need((k-t) % (U*Y) == 0, "exact first-index congruence")
    h = (k-t)//(U*Y)
    need(h > 0 and k == R+1+h*U*Y, "positive first-index quotient")
    numerator, modulus = d-U-a*c, 8*a+15
    need(numerator > 0 and numerator % modulus == 0, "positive exact first exponent quotient")
    gamma = numerator//modulus
    need(d == U+a*c+gamma*modulus, "exact first exponent source equation")
    need(2*(p-1)*(Y+4) < U, "strict rational upper-error estimate")
    need(7*Q > a and p > t, "strict lower-ratio hypotheses")
    need(p != 2*R+1 and 2*R+1-p == v*v, "main index is deliberately different")
    return {"v": v, "p": p, "t": t, "R": R,
            "c_bits": int(c.bit_length()), "k_bits": int(k.bit_length()),
            "eta_positive": True, "zeta_positive": True,
            "h_positive_integer": True, "gamma_positive_integer": True,
            "exact_source_norms_and_quotients": True}


def large_bound_case(N):
    v = N
    p, R = v*v+v+1, v*v+v//2
    exponent_N = N.bit_length()-1
    need(N == 1 << exponent_N and N >= 64, "large sample is a power of two")
    need(v >= 2*exponent_N and 2*p >= 2*exponent_N, "both scales are divisible by N squared")
    need(N*N-1 <= R < 2*N**3, "coarse packed-index range")
    need(p >= R+2 and 2*R+1-p == N*N, "alternative main index")
    need(3*v+2 < 2*p, "proved power bound gives strict ratio error below one")
    need(R.bit_count() == 2 < 2*exponent_N, "central binomial divisibility does not follow")
    return {"N": N, "p": p, "R": R,
            "Y_exponent_of_two": v, "U_exponent_of_two": 2*p,
            "v2_central_binomial": 2, "required_v2": 2*exponent_N,
            "scope": "exact exponent/range checks using the proved growth inequalities; no enormous Pell coordinates constructed"}


def verify():
    exact = [exact_case(v) for v in (2, 4, 6, 8, 12, 16, 24, 32)]
    large = [large_bound_case(N) for N in (64, 256, 4096, 65536)]
    packing = []
    for N in (64, 256, 4096, 65536):
        z = int(g.isqrt(N))
        v = z*(N-1)
        R = v*v+v//2
        S, Tplus = N-1-z//2, z//2
        need(R == S*(N*N-N)+Tplus*(N*N-1), "exact unrestricted positive packing identity")
        need(0 < S < N and 0 < Tplus < N and N*N-1 <= R < N**3, "unrestricted packing ranges")
        need(v >= 2*(N.bit_length()-1), "Y still divisible by N squared")
        packing.append({"N": N, "v": v, "R": R, "S": S, "Tplus": Tplus})
    q, N, v = 8, 16777216, 16719975090
    R, S, Tplus = v*v+v//2, 128193, 864995
    need(N == q**8 and R == 279557567018580495645, "exact sharper-range parameters")
    need(R == S*(N*N-N)+Tplus*(N*N-1), "exact sharper-range packing identity")
    need(0 < S < q**7 and 0 < Tplus < q**7 and S % (q*q) == 1, "sharper numerical block bounds and low residue")
    need(N*N-1 <= R < 2*N**3 and v >= 2*(N.bit_length()-1), "coarse bounds and scale divisibility")
    sharp = {"q": q, "N": N, "v": v, "R": R, "S": S, "Tplus": Tplus,
             "scope": "exact numerical packing and range witness; no full geometric or coefficient-code assignment asserted"}
    return {"status": "PASS",
            "scope": "exact finite Pell subsystem and parameter-family checks; not a solution of the complete encoded system",
            "proof": "../1980/EXPLORATION_RATIO_WITHOUT_SIGNED_INDEX.md",
            "exact_Pell_cases": exact, "large_symbolic_bound_cases": large,
            "unrestricted_positive_packing_cases": packing,
            "sharper_numerical_packing_case": sharp}


if __name__ == "__main__":
    result = verify()
    Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(result["status"], len(result["exact_Pell_cases"]), "exact Pell cases;",
          len(result["large_symbolic_bound_cases"]), "large bound cases;",
          len(result["unrestricted_positive_packing_cases"]), "positive packing cases")
