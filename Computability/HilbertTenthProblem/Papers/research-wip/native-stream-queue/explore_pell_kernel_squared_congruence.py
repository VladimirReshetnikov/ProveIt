#!/usr/bin/env python3
"""Reject a same-cost c^2 congruence repair of the weakened Pell kernel.

This is a scoped kernel obstruction, not a full false-input witness.
The saved receipt is compared by default and changed only with --write.
"""
from pathlib import Path
from math import gcd
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
VERIFICATION = HERE.parent.parent / "verification"
sys.path.insert(0, str(VERIFICATION))

import sympy as sp
import explore_single_product_auxiliary_scale as weakened
from round37_1980_base_two_pell_regression import pell_power


def source_audit():
    previous = weakened.previous
    schedule = [
        (out, op, left, "c2" if out == "jc" else right)
        for out, op, left, right in weakened.SCHEDULE
    ]
    sources = weakened.source_residuals()
    c, j, r, y = (previous.SYM[name] for name in ("c", "j", "r", "y_aux"))
    sources = [sp.expand(source.subs(j, j*c)) for source in sources]
    env = previous.fixed_environment(previous.SYM)
    bridge = previous.previous.previous.previous.previous.bridge
    bridge.baseline.run_schedule(schedule, env)
    U = j*c*c - 2*r - 1
    correction = sources[12]*(U*U-y*y)
    records = []
    for ix, ((left, right), source) in enumerate(zip(weakened.EQUALITIES, sources)):
        actual = sp.expand(env[left]-env[right])
        adjust = correction if ix == 13 else 0
        sign = 1 if sp.expand(actual-source-adjust) == 0 else -1
        assert sp.expand(actual-sign*source-adjust) == 0, ix
        records.append(dict(index=ix, sign=sign, source=sp.sstr(source)))
    primitives, counts = bridge.verify_primitives(schedule, env)
    assert len(primitives) == 75 and counts == {"*": 40, "+": 35}
    assert [ix for ix, (a, b) in enumerate(zip(sources, weakened.source_residuals())) if a != b] == [13, 14]
    return dict(operations=75, multiplications=40, additions_subtractions=35,
                positive_coordinates=len(weakened.NAMES), equations=len(sources),
                replaced_instruction=["jc", "*", "j", "c2"],
                sources=records,
                scope="Exact candidate source audit; no complete soundness claim")


def squared_parameters(A, p, J):
    d, c = pell_power(A, p)
    Delta = A*A-1
    g = gcd(p, c*c)
    assert A >= 2 and p >= 3 and p % 2 == J % 2 == 1
    assert 0 < J < c and J % g == 0
    modulus = c*c//g
    sigma = (-1)**((p-1)//2)
    t = ((-sigma*J-p)//g)*pow(4*p//g, -1, modulus) % modulus
    if (-1)**t != -sigma:
        t += modulus
    s = p+4*p*t
    f, R, i = 2*d*d-1, 2*Delta*c*d, 4*Delta*Delta*d*d
    K = R*R
    assert K == i*c*c == Delta*(f*f-1)
    assert (sigma*s+J) % (c*c) == 0
    assert (-1)**t == -sigma and R > f > 2*c
    if c.bit_length() < 4096:
        assert weakened.q_mod(K, (s-1)//2, c*c) == -J % (c*c)
        assert weakened.q_mod(K, (s-1)//2, f) == -c % f
    return dict(A=A, p=p, J=J, c=c, d=d, Delta=Delta, g=g,
                modulus=modulus, sigma=sigma, t=t, s=s, f=f, R=R, i=i, K=K)


def auxiliary_checks():
    accepted = rejected = 0
    for A in range(2, 10):
        for p in range(3, 16, 2):
            _, c = pell_power(A, p)
            for J in (3, 5, 7, 9, 11, 15):
                if J >= c:
                    continue
                if J % gcd(p, c*c):
                    rejected += 1
                    continue
                squared_parameters(A, p, J)
                accepted += 1
    materialized = []
    for A, p, J in ((2, 3, 9), (4, 3, 15)):
        v = squared_parameters(A, p, J)
        chi, y = pell_power(v["R"], v["s"])
        U, rem = divmod(chi, v["R"])
        j, jrem = divmod(U+J, v["c"]**2)
        o, orem = divmod(U+v["c"], v["f"])
        assert rem == jrem == orem == 0 and min(U, y, j, o) > 0
        assert U == j*v["c"]**2-J == o*v["f"]-v["c"]
        assert v["K"]*(U*U-y*y) == 1-y*y
        materialized.append(dict(A=A, p=p, J=J, c=v["c"],
                                 gcd_p_c_squared=v["g"], auxiliary_index=v["s"],
                                 U_bits=U.bit_length(), y_bits=y.bit_length(),
                                 all_three_auxiliary_equations=True))
    return dict(accepted_modular_cases=accepted, excluded_cases=rejected,
                exact_family_criterion="gcd(p,c^2) divides J",
                materialized=materialized)


def primary_attachment():
    # These are exactly the primary dyadic-balanced family's first/main data.
    D, n, ell, q = 59, 211, 33, 16
    r, p, J, v = n+D-1, n+2*D, 2*(n+D-1)+1, D-1+ell
    assert n*ell == 2*D*D+1
    X, Y = 1 << p, 1 << v
    a, A = Y*(X+1), Y*(X+1)+2
    cmod = weakened.pell_mod(A % p, p, p)[1]
    assert gcd(p, cmod) == 1
    assert q*q <= r < q**4 and X % q**3 == Y % q**3 == 0
    assert X > 4*p*Y and r.bit_count() < 3*(q.bit_length()-1)
    # The changed CRT is evaluated on the actual 138,089-bit main coordinate.
    vaux = squared_parameters(A, p, J)
    # Attach a bounded, odd-index input bridge without asserting compiler data.
    u, W = 3, 8
    mu, kappa = pell_power(A, u)
    delta, rem1 = divmod(kappa-u, A*A-1)
    phi = vaux["c"]-kappa
    rho, rem2 = divmod(mu-a*kappa-W, 4*a+3)
    assert rem1 == rem2 == 0 and min(delta, phi, rho) > 0
    assert mu*mu == 1+(A*A-1)*kappa*kappa
    assert 0 < W < q and u < p
    return dict(q=q, r=r, intended_index=J, actual_index=p,
                X_binary_exponent=p, Y_binary_exponent=v,
                main_c_bits=vaux["c"].bit_length(), gcd_p_c_squared=vaux["g"],
                squared_CRT_modulus_bits=vaux["modulus"].bit_length(),
                auxiliary_index_bits=vaux["s"].bit_length(),
                auxiliary_outputs_materialized=False,
                input_bridge=dict(u=u, W=W, all_four_equations=True),
                scope="Wrong-index kernel plus a numerical bridge; no compiled outer witness")


def verify():
    dependencies = [VERIFICATION / "explore_single_product_auxiliary_scale.py",
                    VERIFICATION / "explore_dyadic_balanced_wrong_index.py"]
    hashes = {str(path.relative_to(HERE.parent.parent)):
              hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()
              for path in dependencies}
    return dict(status="PASS_SCOPED_SQUARED_CONGRUENCE_OBSTRUCTION",
                source=source_audit(), auxiliary=auxiliary_checks(),
                primary=primary_attachment(), dependencies=hashes,
                established_complete_bound=76,
                scope="The same-cost squared congruence does not repair the weakened kernel; full75 soundness remains open")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix(".json")
    normalized = json.loads(json.dumps(result))
    if args.write:
        path.write_text(json.dumps(normalized, indent=2)+"\n", encoding="utf-8")
    else:
        assert normalized == json.loads(path.read_text(encoding="utf-8"))
    print(result["status"])
    print(result["auxiliary"])
    print(result["primary"])
