#!/usr/bin/env python3
"""Independent finite audit; does not import or execute build.py.

Reconstructs the finite algebra directly from the displayed recipe and inert
tile JSON, checks every convolution coefficient, and checks the constructive
Boolean lemma both on a small composite analogue and on the actual modulus.
The universal argument remains PROOF.md.
"""
from pathlib import Path
from math import gcd
import gzip
import hashlib
import json
import random

ROOT = Path(__file__).resolve().parent


def value(name):
    return int.from_bytes(gzip.decompress((ROOT/"payloads"/(name+".bin.gz")).read_bytes()), "little")


def inverse_power(target_t, d, n, B, M):
    """Recover j from B^(4j)=1+5d*target_t mod d*5^n by 5-adic lifting."""
    a = pow(B, 4, M)
    desired = (1+5*d*target_t) % M
    v5d = 0
    temp = d
    while temp % 5 == 0:
        temp //= 5
        v5d += 1
    j, place = 0, 1
    for k in range(n-1):
        modulus = 5**(v5d+2+k)
        candidates = [j+c*place for c in range(5)
                      if pow(a, j+c*place, modulus) == desired % modulus]
        assert len(candidates) == 1
        j = candidates[0]
        place *= 5
    assert pow(a, j, M) == desired
    return j


def check_subset(d, n, target):
    N, T = 5**n, 5**(n-1)
    assert T > 5*d
    M = d*N
    B = pow(2, d, M)
    eps = 0 if target % 5 else 1
    k = (target-eps*B) % (5*d)
    assert k and k < T and gcd(k, T) == 1
    u = ((target-eps*B-k)//(5*d)) % T
    r = pow(k, -1, T)*(u-k*(k-1)//2) % T
    physical = [4*inverse_power((r+i) % T, d, n, B, M) for i in range(k)]
    if eps:
        physical.append(1)
    assert len(set(physical)) == len(physical)
    assert max(physical) < 4*N//5
    assert sum(pow(B, j, M) for j in physical) % M == target % M
    return len(physical)


def audit():
    b, L, d = 125, 8101, 1012625
    beta, K, MC, MFsource = (value(n) for n in ("beta", "K", "MC", "MF_source"))
    B = beta+1
    assert B == 1 << d
    MF = MFsource-beta
    DR = 1 << (125*21)
    DC = K-B*DR
    tiles = json.loads((ROOT/"source/wang943_tiles.json").read_text())
    assert len(tiles) == 943
    E = set(range(943)) | set(range(964,1043,2)) | {1065,1066,1110,1111,1112,2225}
    assert len(E) == 989
    weights = [1024*4**j for j in range(44)]
    coefficients = {}
    for i, tile in enumerate(tiles):
        encoded = sum((label+512) << (10*port) for port,label in enumerate(tile))
        c = 1+sum(weights[40:])
        for bit in range(40):
            if encoded & (1 << bit):
                c += weights[bit]
        coefficients[i] = c
    for port, first in enumerate([1024,1004,984,964]):
        for bit in range(10):
            coefficients[first+2*bit] = weights[10*port+bit]
    coefficients.update({1065:0,1066:0,1110:weights[40],1112:weights[41],
                         1111:weights[42],2225:weights[43]})
    dc = {1:1,40:1,61:1,1113:1}
    for e,c in coefficients.items():
        for band in (3341,4459):
            dc[band-e] = dc.get(band-e,0)+c
    dc = {e:c for e,c in dc.items() if c}
    assert DC == sum(c << (b*e) for e,c in dc.items())
    assert MC == beta-sum(1 << (b*e) for e in E if e != 1)-(2 << (b*1065))
    mu = 1022+sum(weights)
    target_positions = list(range(1004,1023,2))+list(range(1045,1064,2))+[1111,2225]
    expectedMF = 4+(mu << (b*3341))+(mu << (b*4459))
    expectedMF += sum(1 << (b*e) for e in target_positions)
    expectedMF += sum(1 << (b*e) for e in range(6685,7545))
    assert MF == expectedMF

    # Full native-basis coefficient vectors, written separately from the builder.
    expected = {1004+2*j:{964+2*j:1} for j in range(10)}
    expected.update({1045+2*j:{984+2*j:1} for j in range(10)})
    expected.update({1111:{1110:1},2225:{1112:1},3341:coefficients,4459:coefficients})
    convolution = {target:{e:dc.get(target-e,0) for e in E if dc.get(target-e,0)}
                   for target in expected}
    for target,wanted in expected.items():
        assert convolution[target] == {e:c for e,c in wanted.items() if c}
    for target in target_positions+[3341,4459]:
        actualR = {e for e in E if e+21 == target}
        wantedR = {target-21} if target in range(1045,1064,2) else set()
        assert actualR == wantedR
        actualTemporal = {target} & E
        wantedTemporal = ({target} if target in range(1004,1023,2) or target in (1111,2225)
                          else set())
        assert actualTemporal == wantedTemporal
    assert {(3341-e)%L for e in E} & {(4459-e)%L for e in E} == set()
    assert {(1111-e)%L for e in E} & {(2225-e)%L for e in E} == {0}
    assert max(dc)+max(E) == 6684
    assert min(dc) > 0
    mass = 991*(2*sum(coefficients.values())+6)
    assert 4*mass+8 < 1 << b and 2*mu+4 < 1 << b
    assert MC.bit_count()+MF.bit_count() == d
    assert MF.bit_count() == 989 and MC % 4 == 2 and MF % 8 == 4
    assert 0 < MC < beta and 0 < MF < beta and 0 < DC < B

    # Actual integer modular identities, rather than scalar support formulas.
    assert pow(2,125,8101) == 90 and 90*90 % 8101 == 8100
    assert gcd(8101,30) == 1
    for modulus in (5,8101):
        q = B % modulus
        assert (q*q-1) % modulus == (-2) % modulus
        assert (1+q*(DC+B*DR+B)) % modulus == (-3) % modulus
    assert pow(2,4*d,5*d) == 1
    assert pow(2,4*d,625) == 1 and pow(2,4*d,3125) != 1

    # Small composite analogue d=5*41: test every low-cardinality residue
    # class and a shifted high residue. This is an audit of the construction,
    # not the proof of its universal quantifiers.
    small_d, small_n = 205, 6
    small_M = small_d*5**small_n
    assert pow(2,4*small_d,5*small_d) == 1
    small_cases = 0
    for target in range(5*small_d):
        check_subset(small_d,small_n,target)
        small_cases += 1
    for target in (small_M-1,small_M//2,small_M//3,small_M-5):
        check_subset(small_d,small_n,target)
        small_cases += 1

    # Actual large modulus: full subsets are constructed for 32 targets whose
    # chosen cardinalities are <=31. The universal larger-cardinality case is
    # the same cyclic-block proof, not a finite claim based on these examples.
    n = 11
    N, T, M = 5**n,5**(n-1),d*5**n
    assert T > 5*d
    Bmod = pow(2,d,M)
    rng = random.Random(20261022)
    actual_cases = 0
    max_cardinality = 0
    for i in range(32):
        eps = i % 2
        if eps:
            k = [3,8,13,18,23,28][i % 6]
        else:
            k = [1,2,4,6,7,9,11,12,14,16,17,19,21,22,24,26][i//2]
        u = rng.randrange(T)
        target = (eps*Bmod+k+5*d*u) % M
        card = check_subset(d,n,target)
        max_cardinality = max(max_cardinality,card)
        actual_cases += 1

    manifest = json.loads((ROOT/"MANIFEST.json").read_text())
    for name,entry in manifest["ports"].items():
        compressed = (ROOT/entry["file"]).read_bytes()
        raw = gzip.decompress(compressed)
        assert hashlib.sha256(raw).hexdigest() == entry["sha256_raw"]
        assert hashlib.sha256(compressed).hexdigest() == entry["sha256_gzip"]
        nvalue = int.from_bytes(raw,"little")
        assert len(raw) == (nvalue.bit_length()+7)//8 == entry["raw_bytes"]
        assert nvalue.bit_length() == entry["bit_length"]
    result = {
        "status":"PASS", "build_imported":False,
        "finite_recipe":"full exact reconstruction from inert tile JSON",
        "geometry":"all tested native basis vectors; both modular intersections",
        "carry_and_population":"actual fixed integers verified",
        "small_composite_boolean_cases":small_cases,
        "actual_boolean_cases":actual_cases,
        "actual_N":N,"actual_modulus":M,"actual_largest_sample_subset":max_cardinality,
        "total_raw_bytes":manifest["total_raw_bytes"],
        "d":d,"previous_d":1953125,"base_exponent_reduction_percent":48.1536,
        "semantic_boundary":"ordinary proof in PROOF.md plus identified inherited compiler/calibration; no new formal endpoint"
    }
    (ROOT/"INDEPENDENT_CHECKS.json").write_text(json.dumps(result,indent=2)+"\n")
    return result


if __name__ == "__main__":
    print(json.dumps(audit(),indent=2))
