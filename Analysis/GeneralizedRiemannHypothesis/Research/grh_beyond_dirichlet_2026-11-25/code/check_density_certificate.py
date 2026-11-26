#!/usr/bin/env python3
"""Exact finite certificates for the density construction and its new cutoff.

No third-party dependencies. Run from any working directory.
The infinite-set theorem is proved in report.pdf; this script certifies its
finite combinatorial and integer inputs, not the whole asymptotic argument.
The 74-point witness is inherited from ProveIt's polynomial-density report.
It is the translated 878..1358 slice of Gavin Theobald's a(143)<=1360 record
in J. Wroblewski's nonaveraging database (tag 1092044464).
The variance-based coefficient cutoff is the refinement developed here.
"""
from fractions import Fraction
from itertools import combinations
from math import factorial, isqrt
from pathlib import Path
import argparse
import json

SOURCE_SLICE = [
    878,879,882,883,889,891,892,894,898,908,915,916,919,920,
    926,928,929,931,935,945,989,990,993,994,1000,1002,1003,
    1005,1009,1019,1026,1027,1030,1031,1037,1039,1040,1042,
    1046,1056,1211,1212,1215,1216,1222,1224,1225,1227,1231,
    1241,1248,1249,1252,1253,1259,1261,1262,1264,1268,1315,
    1318,1319,1322,1327,1328,1331,1333,1342,1345,1346,1349,
    1354,1355,1358
]
B = sorted(x - 878 for x in SOURCE_SLICE)

def ceildiv(a, b):
    assert a >= 0 and b > 0
    return (a + b - 1) // b

def ceilsqrt(a):
    r = isqrt(a)
    return r if r*r == a else r+1

def irreducible_counts(q, L):
    """Exact counts: q^d = sum_{e|d} e I_q(e)."""
    out = [0] * (L + 1)
    for d in range(1, L + 1):
        lower = sum(e*out[e] for e in range(1, d) if d % e == 0)
        value, rem = divmod(q**d - lower, d)
        assert rem == 0 and value >= 0
        out[d] = value
        assert d * value <= q**d
    return out

def witness_checks():
    assert len(B) == 74 and len(set(B)) == 74 and B[0] == 0 and B[-1] == 480
    bset = set(B)
    pairs = 0
    for x, z in combinations(B, 2):
        assert (x + z) % 2 or (x + z)//2 not in bset
        pairs += 1
    A = {0}
    for j in range(7):
        A |= {a + 3**j for a in A}
    assert len(A) == 128 and max(A) == 1093
    N = 1093
    def scaled(S):
        return sum(127**a * 128**(N-a) for a in S)
    numerator = scaled(B) - scaled(A)
    denominator = 128**N
    assert 1000 * numerator > 16 * denominator
    assert 100000 * 128 * 127**2187 < 128**2187
    # J(127/128)>0.016-0.00001>0.015=3/200.
    assert Fraction(16,1000) - Fraction(1,100000) > Fraction(3,200)
    return {
        "B": B, "cardinality": 74, "max": 480, "midpoint_pairs_checked": pairs,
        "z_numerator": 127, "z_denominator": 128,
        "finite_gain_greater_than": "16/1000",
        "tail_less_than": "1/100000",
        "full_gain_greater_than": "3/200",
        "all_assertions_passed": True
    }

def sphere_check():
    # Nine digits in 0..5, base 11; centered squared norm 105.
    triples = [(1,6,2), (3,3,3), (5,0,4)]
    count = 2**9 * sum(factorial(9)//(factorial(i)*factorial(j)*factorial(k))
                       for i,j,k in triples)
    assert all(i+j+k==9 and j+3*k==12 for i,j,k in triples)
    assert [(9-j-k,j,k) for j in range(10) for k in range(10-j)
            if j+3*k==12] == [(5,0,4),(3,3,3),(1,6,2)]
    M=3**20
    max_bound=(11**9-1)//2
    assert count==1053696 and count>2**20 and 2*max_bound<M
    return {"count":count, "old_count":2**20, "max_bound":max_bound,
            "M":M, "carry_free_digit_bound":10, "all_assertions_passed":True}

def cutoff(q):
    L=480
    counts=irreducible_counts(q,L)
    U=V=0
    for d in range(1,L+1):
        p=127**d
        t=128**d
        h=t-p
        # U >= E X, V >= Var X, using ceilings of each exact rational term.
        U += ceildiv(counts[d]*d*p,h)
        V += ceildiv(counts[d]*d*d*p*t,h*h)
    C=ceilsqrt(7400*V)
    assert (C-1)**2 < 7400*V <= C*C
    R=L+U+C
    old=L+2000000*sum(counts)
    assert Fraction(74,7400)==Fraction(1,100)
    assert Fraction(3,200)-Fraction(1,100)==Fraction(1,200)
    row = {"q":q, "irreducibles_through_480":str(sum(counts)),
           "mean_ceiling_sum":str(U), "variance_ceiling_sum":str(V),
           "standard_deviation_buffer":str(C), "new_R_bound":str(R),
           "new_bit_length":R.bit_length(), "old_R_bound":str(old),
           "old_bit_length":old.bit_length(),
           "old_over_new_display_only":float(Fraction(old,R)),
           "all_assertions_passed":True}
    if q==2:
        assert R+13<2**476
        assert old+13<2**494
        # c_2 >= 1/(2 e L)>1/(6 L)>2^-12, since e<3.
        assert 6*L<2**12
        row.update(binary_density_gap_greater_than="2^(-2^476)",
                   sharper_binary_gap="2^(-R_bound-13)",
                   c2_lower_bound="2^-12",
                   R_plus_13_lt_2_pow_476=True)
    return row

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--output",type=Path,default=Path(__file__).resolve().parents[1]/"data"/"density_certificate.json")
    args=ap.parse_args()
    result={"scope":"Finite certificates only; see report for infinite proof.",
            "witness":witness_checks(),"database_free_sphere":sphere_check(),
            "cutoffs":[cutoff(q) for q in (2,3,4,5,7)]}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print("PASS: 2701 midpoint checks; exact weighted gain and tail bounds.")
    print("PASS: database-free sphere count and range.")
    for row in result["cutoffs"]:
        print(f"q={row['q']}: new cutoff < 2^{row['new_bit_length']}; "
              f"old cutoff < 2^{row['old_bit_length']}")
    print("PASS: binary gap > 2^(-2^476), as a consequence of the paper proof.")
    print(f"Wrote {args.output}")

if __name__=="__main__":
    main()
