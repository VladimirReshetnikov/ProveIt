#!/usr/bin/env python3
"""Independent review audit; no import from build.py or audit_independent.py.

Read the four delivered payloads, recover DC and DR from K, and compare
them with a separately written literal recipe. Geometry is checked against
the recovered coefficient digits, not the builder's sparse representation.
"""
import collections
import gzip
import hashlib
import json
import math
import random
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def require(condition, text):
    if not condition:
        raise ValueError(text)

def main():
    b, length, d = 125, 8101, 1012625
    radix, B = 1 << b, 1 << d
    tiles = json.loads((ROOT / "source/wang943_tiles.json").read_text())
    require(len(tiles) == 943 and len(set(map(tuple, tiles))) == 943, "tile cardinality")
    copy = [[offset+2*j for j in range(10)] for offset in (1024,1004,984,964)]
    anchors = [1110,1112,1111,2225]
    dummy = [1065,1066]
    E = set(range(943)) | set(sum(copy, [])) | set(anchors) | set(dummy)
    require(len(E) == 989, "native cardinality")
    W = [1024*4**j for j in range(44)]
    c = {}
    for index, tile in enumerate(tiles):
        c[index] = 1+sum(W[40:])
        for slot, label in enumerate(tile):
            bits = label+512
            require(512 <= bits < 1024, "edge code range")
            for bit in range(10):
                c[index] += ((bits >> bit) & 1)*W[10*slot+bit]
    for slot in range(4):
        for bit in range(10):
            c[copy[slot][bit]] = W[10*slot+bit]
    for j, exponent in enumerate(anchors):
        c[exponent] = W[40+j]
    c.update({exponent:0 for exponent in dummy})
    require(set(c) == E, "coefficient support")

    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    ports = {}
    for name in ("beta","K","MC","MF_source"):
        info = manifest["ports"][name]
        compressed = (ROOT / info["file"]).read_bytes()
        raw = gzip.decompress(compressed)
        require(hashlib.sha256(raw).hexdigest() == info["sha256_raw"], "raw payload hash")
        require(hashlib.sha256(compressed).hexdigest() == info["sha256_gzip"], "gzip payload hash")
        ports[name] = int.from_bytes(raw, "little")
        require(len(raw) == (ports[name].bit_length()+7)//8, "minimal encoding")
    require(ports["beta"] == B-1, "base port")
    DC, DR = ports["K"] % B, ports["K"] // B
    require(DR == 1 << (21*b), "spatial coefficient")
    digits = {}
    temporary = DC
    exponent = 0
    while temporary:
        digit = temporary & (radix-1)
        if digit:
            digits[exponent] = digit
        temporary >>= b
        exponent += 1
    expected = collections.defaultdict(int, {shift:1 for shift in (1,40,61,1113)})
    for e, coefficient in c.items():
        for target in (3341,4459):
            expected[target-e] += coefficient
    expected = {e:v for e,v in expected.items() if v}
    require(max(expected.values()) < radix, "DC digit overflow")
    require(digits == expected, "recovered DC differs from literal recipe")

    # Each tuple is target, DC-source, DR-source, temporal-source.
    targets = [(1004+2*j,964+2*j,None,1004+2*j) for j in range(10)]
    targets += [(1045+2*j,984+2*j,1024+2*j,None) for j in range(10)]
    targets += [(1111,1110,None,1111),(2225,1112,None,2225)]
    checks = 0
    for t, dc_source, dr_source, temporal_source in targets:
        for e in E:
            require(digits.get(t-e,0) == int(e == dc_source), "DC overlap identity")
            require(int(t-e == 21) == int(e == dr_source), "DR overlap identity")
            require(int(t == e) == int(e == temporal_source), "temporal overlap identity")
            checks += 3
    for t in (3341,4459):
        for e in E:
            require(digits.get(t-e,0) == c[e], "clause identity")
            require(t-e != 21, "clause DR contamination")
            checks += 2
    require(checks == 69230, "check ledger")
    require({(3341-e)%length for e in E}.isdisjoint({(4459-e)%length for e in E}), "dirty paired bands")
    require({(1111-e)%length for e in E} & {(2225-e)%length for e in E} == {0}, "anchor ambiguity")
    require({(x,y) for x in E for y in E if x-y == 1114} == {(2225,1111)}, "anchor difference")
    require(not any(x-1118 in E for x in E), "band difference")
    require(not any(x-1116 in E for x in E), "reflected contamination difference")

    mu = 1022+sum(W)
    MF = ports["MF_source"]-ports["beta"]
    expected_MF = 4+sum(mu << (b*t) for t in (3341,4459))
    expected_MF += sum(1 << (b*t) for t,*_ in targets)
    expected_MF += sum(1 << (b*t) for t in range(6685,7545))
    expected_MC = B-1-sum(1 << (b*e) for e in E if e != 1)-(2 << (1065*b))
    require(MF == expected_MF and ports["MC"] == expected_MC, "mask recipe")
    require(MF.bit_count() == 989 and ports["MC"].bit_count() == d-989, "population")
    require(0 < MF < B-1 and 0 < ports["MC"] < B-1, "mask bounds")
    require(MF%8 == 4 and ports["MC"]%4 == 2, "mask residues")
    mass = (len(E)+2)*(2*sum(c.values())+6)
    require(4*mass+8 < radix and 2*mu+4 < radix, "carry/slack estimate")
    require(max(digits)+max(E) == 6684 < 6685 <= 7544 < length, "zero-field support bound")

    arithmetic = {}
    for m in (5,8101):
        rho = pow(2,b,m)
        bm = pow(2,d,m)
        bracket = (1+bm*(DC+bm*DR+bm))%m
        require(rho*rho%m == m-1 and bm == rho, "order-four residues")
        require(DC%m == (1+3*rho)%m and DR%m == rho, "DC/DR residues")
        require(bracket == (-3)%m and math.gcd(bracket*(bm*bm-1),m) == 1, "rank unit")
        arithmetic[str(m)] = {"rho":rho,"DC":DC%m,"DR":DR%m,"bracket":bracket}
    require(pow(2,4*d,625) == 1 and pow(2,4*d,3125) != 1, "exact 5-adic order")
    require(pow(2,4*d,8101) == 1 and math.gcd(8101,5) == 1, "CRT order")
    # Small exhaustive subgroup instances verify the arithmetic pattern.
    subgroup_cases = []
    for n in (1,2,3,4,5):
        N, T = 5**n, 5**(n-1)
        modulus = d*N
        weight = pow(2,4*d,modulus)
        orbit = {pow(weight,j,modulus) for j in range(T)}
        require(orbit == {1+5*d*t for t in range(T)}, "subgroup enumeration")
        subgroup_cases.append({"N":N,"orbit_length":T})
    # At an actual sufficiently large N, check the cyclic-cardinality formula.
    N, T = 5**11, 5**10
    modulus = d*N
    require(T > 5*d, "large-N precondition")
    bm = pow(2,d,modulus)
    rng = random.Random(1012625)
    cardinality_cases = 0
    for z in [-2,-1,0,1,2,modulus-1] + [rng.randrange(modulus) for _ in range(100)]:
        epsilon = 0 if z%5 else 1
        k = (z-epsilon*bm)%(5*d)
        require(0 < k < T and math.gcd(k,T) == 1, "cyclic cardinality")
        u = ((z-epsilon*bm-k)//(5*d))%T
        r = ((u-k*(k-1)//2)*pow(k,-1,T))%T
        t_sum = (k*r+k*(k-1)//2)%T
        require((k+5*d*t_sum+epsilon*bm-z)%modulus == 0, "Boolean target formula")
        cardinality_cases += 1
    receipt = {
        "status":"PASS", "independent_of_build_module":True,
        "payload_recipe_comparisons":4, "native_basis_identities":checks,
        "paired_bands_disjoint":True, "unique_anchor_offset":True,
        "zero_padding_bound":6684, "mass_bit_length":mass.bit_length(),
        "rank_residues":arithmetic, "subgroup_cases":subgroup_cases,
        "large_N_cardinality_cases":cardinality_cases,
        "scope":"Independent finite recipe/carry/geometry/rank-arithmetic audit; universal semantics and lemma reviewed mathematically in EXTERNAL_REVIEW.md."
    }
    (ROOT / "EXTERNAL_REVIEW_CHECKS.json").write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps(receipt,indent=2))

if __name__ == "__main__":
    main()
