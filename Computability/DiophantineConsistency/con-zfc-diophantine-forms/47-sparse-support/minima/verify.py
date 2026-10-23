#!/usr/bin/env python3
"""Exact, standard-library audit of the minimum-norm circuits.

No interpolation or random testing is used. Degree propagation supplies an
upper bound plus the exact coefficient at that bound after all 15 variables
are set to T. A universally verified polynomial identity resolves the only
degree cancellation needed by the upper bound.
"""
import argparse
import gzip
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path
sys.dont_write_bytecode = True
from build_minima import build

ROOT = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def git_blob(raw):
    return hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest()

# Exact integer polynomials in four formal fixed coefficient leaves.
ZERO = (0, 0, 0, 0)
def const(n):
    return {ZERO: n} if n else {}
def var(i):
    e = [0]*4
    e[i] = 1
    return {tuple(e): 1}
def add(p, q, sign=1):
    r = p.copy()
    for e, c in q.items():
        r[e] = r.get(e, 0)+sign*c
        if not r[e]:
            del r[e]
    return r
def mul(p, q):
    r = {}
    for e, a in p.items():
        for f, b in q.items():
            k = tuple(x+y for x, y in zip(e, f))
            r[k] = r.get(k, 0)+a*b
    return {e: a for e, a in r.items() if a}
def square(p):
    return mul(p, p)

# (multivariate degree upper bound, exact diagonal coefficient at that bound).
def dconst(n):
    return 0, const(n)
def dadd(a, b, sign=1):
    n = max(a[0], b[0])
    return n, add(a[1] if a[0] == n else {},
                  b[1] if b[0] == n else {}, sign)
def dmul(a, b):
    return a[0]+b[0], mul(a[1], b[1])

def verify_gap_identity():
    U, V, e = [var(i) for i in range(3)]
    y = add(V, e)
    original = add(mul(U, add(square(V), square(y), -1)), square(y))
    factored = add(square(V),
                   mul(mul(add(U, const(1), -1), e), add(add(V, V), e)), -1)
    require(original == factored, "universal auxiliary gap identity failed")
    return len(original)

def topology(d):
    witnesses, fixed = d["witnesses"], d["fixed_numerals"]
    require(len(witnesses) == 15 and len(set(witnesses)) == 15, "witness list")
    require(set(fixed) == {"Bm1", "Kconstant", "MC", "MF"}, "fixed tuple ports")
    known = set(witnesses+fixed)
    dependencies = {}
    for row in d["source"]:
        require(len(row) == 4, "malformed gate")
        name, op, a, b = row
        require(name not in known and op in ("+", "-", "*"), "gate name or opcode")
        for operand in (a, b):
            require(type(operand) is int or operand in known,
                    "forward reference: "+str(operand))
        dependencies[name] = [x for x in (a, b) if type(x) is not int]
        known.add(name)
    used, todo = set(), [d["output"]]
    while todo:
        name = todo.pop()
        if name not in used:
            used.add(name)
            todo.extend(dependencies.get(name, []))
    require(set(dependencies) <= used, "dead arithmetic gate")
    require(set(witnesses+fixed) <= used, "dead supplied input")
    return dict(Counter(row[1] for row in d["source"]))

def degree_certificate(d):
    # These literal patterns identify the exact subexpression being replaced.
    rows = {row[0]: row[1:] for row in d["source"]}
    expected = {
        "gap_y": ["+", "aux_u_rhs", "auxiliary_gap"],
        "aux_y2": ["*", "gap_y", "gap_y"],
        "H2": ["*", "aux_u_rhs", "aux_u_rhs"],
        "aux_square_gap": ["-", "H2", "aux_y2"],
        "L17": ["*", "R16", "aux_square_gap"],
        "norm_aux": ["+", "L17", "aux_y2"],
    }
    for name, expression in expected.items():
        require(rows.get(name) == expression, "auxiliary sub-DAG mismatch: "+name)
    env = {x: (1, const(1)) for x in d["witnesses"]}
    env.update({x: (0, var(j)) for j, x in enumerate(d["fixed_numerals"])})
    def value(x):
        return dconst(x) if type(x) is int else env[x]
    for name, op, a, b in d["source"]:
        if name == "norm_aux":
            U, V, e = [env[x] for x in ("R16", "aux_u_rhs", "auxiliary_gap")]
            # U(V^2-(V+e)^2)+(V+e)^2 = V^2-(U-1)e(2V+e).
            env[name] = dadd(dmul(V, V),
                            dmul(dmul(dadd(U, dconst(1), -1), e),
                                 dadd(dadd(V, V), e)), -1)
        elif op == "*":
            env[name] = dmul(value(a), value(b))
        else:
            env[name] = dadd(value(a), value(b), -1 if op == "-" else 1)
    degree, leading = env[d["output"]]
    wanted = {(28, 0, 0, 0): 16,
              (24, 0, 0, 0): 256,
              (22, 0, 0, 0): 16}
    require(degree == 44 and leading == wanted, "exact degree certificate mismatch")
    return {
        "total_degree_upper_bound": degree,
        "attained_diagonal_degree": degree,
        "diagonal_leading_coefficient": "16*beta^28 + 256*beta^24 + 16*beta^22",
        "positivity_reason": "Every displayed coefficient is positive and beta>0.",
        "symbolic_coefficients": [
            {"powers": list(e), "coefficient": c} for e, c in sorted(leading.items())
        ],
        "gap_identity_checked_by_exact_ring_expansion": True,
    }

def fixed_values():
    d = json.loads((ROOT / "fixed_coefficients.json").read_text())
    out = {}
    for row in d["ports"]:
        encoded = (ROOT / row["file"]).read_bytes()
        raw = gzip.decompress(encoded)
        require(sha(encoded) == row["gzip_sha256"], "compressed payload hash")
        require(sha(raw) == row["raw_sha256"] and len(raw) == row["raw_bytes"],
                "uncompressed payload hash or length")
        n = int.from_bytes(raw, "little", signed=False)
        require(n.bit_length() == row["bit_length"] and n > 0, "port value or size")
        require(raw == n.to_bytes((n.bit_length()+7)//8, "little"), "nonminimal magnitude")
        out[row["circuit_port"]] = n
    require(set(out) == {"Bm1", "Kconstant", "MC", "MF"}, "complete tuple required")
    require(out["Bm1"] == (1 << 1064921)-1, "native beta mismatch")
    upstream = json.loads((ROOT / "upstream/COEFFICIENT_BINDING.json").read_text())
    require(upstream["ports"] == {
        "Bm1": "beta", "Kconstant": "K", "MC": "MC", "MF": "MF_source"},
        "upstream tuple alias mismatch")
    return out

def evaluate_mod(d, witnesses, modulus):
    require(modulus > 1, "modulus must be greater than 1")
    require(len(witnesses) == 15 and all(x > 0 for x in witnesses),
            "supply 15 strictly positive integers")
    env = {name: n % modulus for name, n in fixed_values().items()}
    env.update({name: n % modulus for name, n in zip(d["witnesses"], witnesses)})
    def value(x):
        return x % modulus if type(x) is int else env[x]
    for name, op, a, b in d["source"]:
        x, y = value(a), value(b)
        env[name] = (x*y if op == "*" else x+y if op == "+" else x-y) % modulus
    return env[d["output"]]

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--receipt", default="verification_receipt.json")
    args = parser.parse_args()
    pins = json.loads((ROOT / "SOURCE_PINS.json").read_text())
    for p in pins["exact_inherited_files"]:
        raw = (ROOT / p["local_file"]).read_bytes()
        require(len(raw) == p["bytes"] and sha(raw) == p["sha256"],
                "pinned byte mismatch: "+p["local_file"])
        require(git_blob(raw) == p["git_blob_sha1"] ==
                p["expected_upstream_git_blob_sha1"],
                "upstream Git blob mismatch: "+p["local_file"])
        require(len(p["source_commit"]) == 40, "full immutable commit required")
    values = fixed_values()
    gap_terms = verify_gap_identity()
    results = []
    for gates in (75, 76, 78):
        file = ("gap_minima"+str(gates)+".json" if gates != 78
                else "upstream/ordinary_gap_sos78.json")
        d = json.loads((ROOT / file).read_text())
        if gates != 78:
            require(d == build(coupled=(gates == 75)), "deterministic rebuild mismatch")
            require(d["coefficient_binding"] == "fixed_coefficients.json", "binding link")
        ledger = topology(d)
        require(len(d["source"]) == gates, "operation count")
        require(ledger["*"] == 40, "multiplication count")
        if gates != 78:
            require(ledger == {"*": 40, "+": gates-55, "-": 15}, "ledger")
        cert = degree_certificate(d)
        results.append({"file": file, "sha256": sha((ROOT/file).read_bytes()),
                        "operations": gates, "ledger": ledger,
                        "all_gates_and_ports_live": True, **cert})
    result = {
        "status": "PASS",
        "method": "Exact finite ring calculation and leading coefficient propagation; no sampling.",
        "inherited_files_authenticated": len(pins["exact_inherited_files"]),
        "complete_fixed_tuple_bits": {k: v.bit_length() for k, v in values.items()},
        "auxiliary_identity_terms": gap_terms,
        "results": results,
        "scope": "Certificates establish byte binding, circuit reproduction, liveness, "
                 "counts and degree. MINIMA_PROOF.txt proves the unbounded minimum "
                 "lemma. The ordinary Pell/compiler and ZFC interpretation are "
                 "imported mathematical dependencies, not proved by these checks.",
    }
    receipt = Path(args.receipt)
    if not receipt.is_absolute():
        receipt = ROOT / receipt
    receipt.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
