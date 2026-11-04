#!/usr/bin/env python3
"""Exact finite gcd checks and a small CRT/carrier divisibility diagnostic.

The symbolic Pell gcd is checked separately by the sibling GMP program.
This script does not construct the huge symbolic Pell ordinate or a graph zero.
"""
import gzip
import hashlib
import json
import math
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")

ROOT = Path(__file__).resolve().parents[2]
DIR = ROOT / "candidates/ten-positive-qcube-product-square/coefficients"
entries = {
    "beta": ("beta.bin.gz", "07d42a69e7593ac08bcb2957c965c02f179588b0c3b232c3c640258d0aaeab04", "0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d", 590069),
    "K0": ("K.bin.gz", "35ad71ca5349bf78c996ac983a7cea6944260ed9f35c61c2b70770f5888d52ce", "0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f", 592884),
    "MC": ("MC.bin.gz", "71ecc4fe568471f83978d00ee7a4e03614203d6af36611c0660dbd4fd3eb2276", "6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4", 590069),
    "MF": ("MF_source.bin.gz", "ea069f55029bab743997b0a79b0535d5ad558686848a03cb41d72faf596a6a6a", "48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737", 590070),
}
ports = {}
candidate_bytes = (ROOT / "research/trace74-mask-coordinate-probe/candidate.json").read_bytes()
assert hashlib.sha256(candidate_bytes).hexdigest() == "dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353"
candidate = json.loads(candidate_bytes)
assert candidate["operations"] == 74
assert candidate["fixed_numerals"] == ["beta", "K0", "MC", "MF"]
assert candidate["witnesses"] == ["J", "F", "C", "i", "T", "w", "s", "n", "eta", "zeta"]
assert set(candidate["coefficient_binding"]["ports"]) == set(entries)
for name, (filename, compressed_hash, raw_hash, bits) in entries.items():
    metadata = candidate["coefficient_binding"]["ports"][name]
    assert (metadata["file"], metadata["parent_gzip_sha256"], metadata["raw_sha256"], metadata["bits"]) == (filename, compressed_hash, raw_hash, bits)
    compressed = (DIR / filename).read_bytes()
    assert hashlib.sha256(compressed).hexdigest() == compressed_hash
    raw = gzip.decompress(compressed)
    assert hashlib.sha256(raw).hexdigest() == raw_hash
    ports[name] = int.from_bytes(raw, "little")
    assert ports[name].bit_length() == bits
K0 = ports["K0"]
B, r = 590069, 3056651345
h = (1 << B) - 1
assert ports["beta"] == h
xmod = 1 << (r % B)
wmod = 1 << ((r - B) % B)
assert (r % B, (r - B) % B) == (93925, 93925)
assert math.gcd(h, 4*xmod + 3) == 1
assert math.gcd(h, K0+wmod) == 1
print("candidate metadata, four pinned payloads, symbolic beta and two gcds PASS")

def ordinate(index, coefficient):
    a, b = 0, 1
    for _ in range(index):
        a, b = b, coefficient*b-a
    return a

def crt(residues, moduli):
    value, modulus = 0, 1
    for residue, next_modulus in zip(residues, moduli):
        assert math.gcd(modulus, next_modulus) == 1
        value += modulus * (((residue-value)*pow(modulus, -1, next_modulus)) % next_modulus)
        modulus *= next_modulus
    return value, modulus

# Small analogous power-matching instance from the sibling packet.
B, n, r = 7, 63, 77
q = 1 << B
h, Y, X = q-1, q**3, 1 << r
D, H = X*Y, 4*Y*(X+1)-1
w, K0, MC, MF = X//q, 1, 2, q
P = X*Y**2
k = 2*ordinate(n, 4*P+2)
c = ordinate(r, 2*Y*(X+1)+2)
eta, zeta = c-k*Y, (k*(Y+1))-c
assert eta > 0 and zeta > 0 and eta+zeta == k
assert math.gcd(c, q*q-1) == math.gcd(c, D) == math.gcd(c, h) == 1
assert math.gcd(h, D) == math.gcd(H, h*D) == math.gcd(K0+w,h) == 1
Rj = MC+q*MF
gD = ((k-1-Rj)*pow(q*q-1, -1, D)) % D
gc = ((-r-Rj)*pow(q*q-1, -1, c)) % c
gh = -pow(K0+w, -1, h) % h
G0, period = crt((gD,gc,gh),(D,c,h))
G = G0 - period*(1 + (Rj//(q*q-1) + 1)//period)
R = (q*q-1)*G+Rj
C = q*(q-1)-G
e = k-R-1
Breg = (K0+w)*C-1
Kreg = X*(3*c-2*X)+2
assert G < 0 and R < 0 and C > 0 and 1+C >= q
assert (-R-r) % c == 0 and e % D == 0 and Breg % h == 0 and Breg >= 0
assert Kreg % H == 0
assert (D*Breg+h*e) % (h*D) == 0

# Evaluate the actual carrier expression at arbitrary positive i,T,v7.
i, T, v7 = 1, 1, 1
A = Y*(X+1)
Delta = A*(A+2)
E = 1+P*(P+1)*k*k
f = 1+2*Delta*(i*c*c)**2*E
V = f*(c*T-R)-c
Z = h*D*(H*(v7-V*V*Breg)+Kreg)-H*(D*Breg+h*e)
M = h*D*H
assert Z % M == 0
print("small analogous B=7: CRT, rank sign, carrier divisibility PASS")
print("No full output zero or iPRA theorem is asserted.")
