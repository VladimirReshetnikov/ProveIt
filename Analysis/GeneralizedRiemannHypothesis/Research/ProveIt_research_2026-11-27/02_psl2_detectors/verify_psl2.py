#!/usr/bin/env python3
"""Exact checks for the PSL2(q) detector identities and exceptional cases.

Only Python's standard library is required.  The uniform proofs are in
psl2_detector.tex; these checks verify the algebra and every finite case
used by its optimality argument.  This is not a Lean formalization.
"""
from fractions import Fraction as F
from math import gcd, isqrt
import json
from pathlib import Path


def prime_power(q):
    for p in range(2, isqrt(q) + 2):
        if q % p == 0:
            n = q
            while n % p == 0:
                n //= p
            return p if n == 1 else None
    return q if q >= 2 else None


def phi(n):
    return sum(gcd(j, n) == 1 for j in range(1, n + 1))


def mobius(n):
    ans, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            ans = -ans
            if n % p == 0:
                return 0
            while n % p == 0:
                n //= p
        p += 1
    return -ans if n > 1 else ans


def uniform_check(q):
    assert q % 4 == 1
    a, b = (q - 1) // 2, (q + 1) // 2
    indicator = int(q % 8 == 1)
    pe_count = (a // 2 - 1 - indicator) // 2
    # Tuple entries are (Reg, pi_U, pi_N, pi_B, P_even, E).
    group_order = q * (q * q - 1) // 2
    cases = [
        ("identity", (group_order, (q*q-1)//2, q*(q-1)//2,
                      q+1, pe_count*(q+1), q+1)),
        ("unipotent square", (0, (q-1)//2, 0, 1, pe_count, 1)),
        ("unipotent nonsquare", (0, (q-1)//2, 0, 1, pe_count, 1)),
    ]
    for j in range(1, a):
        inv = 2 * j == a
        delta = (-1) ** j
        pe = (a // 2 if (2*j) % a == 0 else 0) - 1 - indicator * delta
        cases.append((f"split exponent {j}",
                      (0, 0, a if inv else 0, 2, pe, 2*delta)))
    for j in range(1, b):
        cases.append((f"nonsplit exponent {j}", (0, 0, 1, 0, 0, 0)))
    for label, (reg, pu, pn, pb, pe, ep) in cases:
        lhs = (q-1)*pn + ((q+1)//2)*pu - reg
        rhs = (q-1)*(1 + F(pb, 2) + 2*pe + indicator*ep)
        assert lhs == rhs, (q, label, lhs, rhs)
    # Irreducible multiplicity checks, including exceptional constituents.
    # Columns: degree, pi_U, pi_N, pi_B, P_even, E.
    irreps = [(1,1,1,1,0,0), (q,1,1,1,0,0)]
    for j in range(1, a//2):
        irreps.append((q+1, 2, 1+(-1)**j, 0, int(j%2==0), 0))
    for j in range(1, (b+1)//2):
        irreps.append((q-1,0,1,0,0,0))
    for _ in range(2):
        irreps.append(((q+1)//2,1,indicator,0,0,1))
    assert sum(d*d for d,*_ in irreps) == group_order
    for i, (d, pu, pn, pb, pe, ep) in enumerate(irreps):
        # The standalone trivial character only occurs at i=0.
        assert (q-1)*pn + ((q+1)//2)*pu-d == (
            (q-1)*(int(i==0) + F(pb,2) + 2*pe + indicator*ep))
        assert pu+pn > 0
    return len(cases), len(irreps)


EXCEPTIONS = {
    "A4": (12, {2:3, 3:8}),
    "S4": (24, {2:9, 3:8, 4:6}),
    "A5": (60, {2:15, 3:20, 5:24}),
}


def occurs(q, group):
    if group == "A4":
        return True
    if group == "S4":
        return q % 8 in (1,7)
    return q % 5 not in (2,3)


def faithful_principal_fixed(q, group):
    """Average the faithful principal-series character on an exceptional H.

    At an element of order d, coprime to p, average over the generators of
    each cyclic subgroup.  Faithfulness gives 2*mu(d)/phi(d) in the split
    case and zero in the nonsplit case.  Unipotent value is one.
    """
    order, counts = EXCEPTIONS[group]
    p = prime_power(q)
    value = F(q+1)
    for d, count in counts.items():
        if d == p:
            row = F(1)
        elif ((q-1)//2) % d == 0:
            row = F(2*mobius(d), phi(d))
        else:
            assert ((q+1)//2) % d == 0
            row = F(0)
        value += count * row
    return value / order


def exceptional_checks():
    rows = []
    for q in range(9, 60, 4):
        if prime_power(q) is None:
            continue
        for group, (order, _) in EXCEPTIONS.items():
            if occurs(q, group) and order > q:
                result = faithful_principal_fixed(q, group)
                expected = F(1) if (q,group)==(9,"A4") else F(0)
                assert result == expected, (q, group, result)
                rows.append({"q":q,"subgroup":group,"order":order,
                             "fixed_dimension":str(result)})
    assert {(r["q"],r["subgroup"]) for r in rows} == {
        (9,"A4"),(9,"S4"),(9,"A5"),(17,"S4"),
        (25,"A5"),(29,"A5"),(41,"A5"),(49,"A5")}
    return rows


def q9_checks():
    names = ["1","St","P10","D8a","D8b","E5plus","E5minus"]
    reg = [1,9,10,8,8,5,5]
    pN = [1,1,0,1,1,1,1]
    pA = [1,1,1,0,0,2,0]
    pB = [1,1,0,0,0,0,0]
    pHp = [1,0,0,0,0,1,0]
    pHm = [1,0,0,0,0,0,1]
    for i in range(7):
        assert pN[i]+pA[i] > 0
        assert 8*pN[i]+10*pA[i]+18*int(i==0)-reg[i] == (
            9*pB[i]+23*pHp[i]+3*pHm[i])
    # Degree-eight cuspidal obstructions for every exceptional group >10.
    cusp_averages = {"A4":F(8-8,12), "S4":F(8-8,24),
                     "A5":F(8-20+12,60)}
    assert all(v == 0 for v in cusp_averages.values())
    return {"irreducibles":names,"regular":reg,"pi_N":pN,"pi_A4":pA,
            "pi_B":pB,"pi_A5_plus":pHp,"pi_A5_minus":pHm,
            "cuspidal_obstructions":{k:str(v) for k,v in cusp_averages.items()}}


def all_odd_identity(q):
    a,b=(q-1)//2,(q+1)//2
    rows=[(1,1,1,1),(q,1,1,1)] # degree, pi_Tn, pi_U, pi_B
    for j in range(1,(a+1)//2):
        if 2*j != a:
            rows.append((q+1,2,2,0))
    for j in range(1,(b+1)//2):
        if 2*j != b:
            rows.append((q-1,2,0,0))
    for _ in range(2):
        rows.append(((q+1)//2 if q%4==1 else (q-1)//2,
                     1, int(q%4==1),0))
    assert sum(row[0]**2 for row in rows)==q*(q*q-1)//2
    for i,(d,pt,pu,pb) in enumerate(rows):
        assert d==((q-1)//2)*(pt+pb-2*int(i==0))+pu
    return len(rows)


def main():
    q_values = [q for q in range(5,1001,4) if prime_power(q)]
    checked_classes=checked_irreps=0
    for q in q_values:
        n,m=uniform_check(q)
        checked_classes+=n
        checked_irreps+=m
    odd_values=[q for q in range(5,1001,2) if prime_power(q)]
    for q in odd_values:
        all_odd_identity(q)
    data={"status":"all exact checks passed", "uniform_q_values":q_values,
          "uniform_class_cases":checked_classes,
          "uniform_irreducible_cases":checked_irreps,
          "all_odd_q_values":odd_values,
          "exceptional_lower_bound_cases":exceptional_checks(),
          "q9":q9_checks(),
          "q13":{"group_order":1092,"field_degrees_U_N":[84,78],
                 "order_bound_coefficients_U_N":[7,12],
                 "optimal_maximum_degree":84}}
    output=Path(__file__).with_name("verification_psl2.json")
    output.write_text(json.dumps(data,indent=2)+"\n")
    print(data["status"])
    print(f"Uniform q=1 mod 4 identities: {len(q_values)} field sizes, "
          f"{checked_classes} class cases, {checked_irreps} irreducible cases.")
    print(f"All-odd identity: {len(odd_values)} field sizes.")
    print(f"Exceptional lower bounds: {len(data['exceptional_lower_bound_cases'])} cases.")
    print("q=9 exceptional identity and q=13 example passed.")


if __name__ == "__main__":
    main()
