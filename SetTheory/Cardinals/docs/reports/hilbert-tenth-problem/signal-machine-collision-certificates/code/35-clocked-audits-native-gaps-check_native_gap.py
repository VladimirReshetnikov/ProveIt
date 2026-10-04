#!/usr/bin/env python3
"""Independent, source-bound static certificate checks. Standard library only.

Read candidate files as bytes/text/JSON, never import or execute them. Write all
receipts to an explicitly supplied, previously absent external directory.
Concrete Pell recurrences below produce integer fixtures, not a proof-assistant
check or a signal/counter-machine simulator. No network or subprocess use.
"""
import argparse
from fractions import Fraction
from hashlib import sha256, sha1
import json
from math import gcd, lcm
from pathlib import Path

PROOF_HASH = "8cc5911e528d0555ee89fe63f0e30b8a3eac4a32e3e4237ee9b00a38107a7d1b"
MANIFEST_HASH = "224da321a9eb86b8a296948d6429ea164b245975fd4a4edab7b361b471c6c382"
PELL_HASH = "993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a"
PELL_BLOB = "6ede8ed67569fc1ddf2b4c09f0feb30ca42fca7e"


def check(test, label):
    if not test:
        raise ValueError(label)


def digest(data):
    return sha256(data).hexdigest()


def snapshot(source):
    result = {}
    for path in sorted(source.rglob("*")):
        check(not path.is_symlink(), "No source symlinks")
        info = path.stat()
        result[str(path.relative_to(source))] = {
            "mode": info.st_mode, "size": info.st_size,
            "mtime_ns": info.st_mtime_ns,
            "sha256": digest(path.read_bytes()) if path.is_file() else None,
        }
    return result


def bind(source):
    check(digest((source / "PROOF.md").read_bytes()) == PROOF_HASH, "Proof pin")
    check(digest((source / "MANIFEST.json").read_bytes()) == MANIFEST_HASH, "Manifest pin")
    manifest = json.loads((source / "MANIFEST.json").read_text())
    names = set()
    for item in manifest["files"]:
        rel = Path(item["file"])
        check(not rel.is_absolute() and ".." not in rel.parts, "Safe manifest path")
        check(str(rel) not in names, "Unique manifest entry")
        names.add(str(rel))
        data = (source / rel).read_bytes()
        check(len(data) == item["bytes"] and digest(data) == item["sha256"],
              "Manifest entry " + str(rel))
    actual = {str(p.relative_to(source)) for p in source.rglob("*") if p.is_file()}
    check(actual == names | {"MANIFEST.json"}, "Complete manifested file set")
    copies = json.loads((source / "SOURCE_PINS.json").read_text())
    for item in copies:
        data = (source / item["file"]).read_bytes()
        check(len(data) == item["bytes"] and digest(data) == item["sha256"], "Dependency pin")
        check(item["executed"] is False and item["read_as_inert_text"] is True,
              "Declared inert dependency")
    pell = (source / "dependencies/pell-source.lean").read_bytes()
    check(digest(pell) == PELL_HASH, "Pell byte pin")
    check(sha1(b"blob " + str(len(pell)).encode() + b"\0" + pell).hexdigest() == PELL_BLOB,
          "Pell Git blob object identifier")
    lines = pell.decode().splitlines()
    check(lines[759] == "theorem matiyasevic {a k x y} :", "Matiyasevic location")
    check(lines[859] == "theorem eq_pow_of_pell {m n k} :", "Power theorem location")
    statement_a = "\n".join(lines[759:766])
    statement_b = "\n".join(lines[859:864])
    for fragment in ("k ≤ y", "0 < v", "y * y ∣ v", "t ≡ k [MOD 4 * y]"):
        check(fragment in statement_a, "Matiyasevic hypothesis " + fragment)
    for fragment in ("0 < k", "0 < n", "(a - n)", "m < t", "n ≤ w ∧ k ≤ w"):
        check(fragment in statement_b, "Power hypothesis " + fragment)
    return {"files": len(actual), "dependency_copies": len(copies),
            "proof_sha256": PROOF_HASH, "manifest_sha256": MANIFEST_HASH,
            "pell_sha256": PELL_HASH, "pell_git_blob_sha1": PELL_BLOB,
            "theorem_statements": [statement_a, statement_b]}


# Integer polynomials represented by coefficients keyed by sorted tuples of
# variable names, including repetitions: (x,x,y) means x^2*y.
class P:
    def __init__(self, value=0):
        if isinstance(value, dict):
            self.d = {k: v for k, v in value.items() if v}
        elif isinstance(value, str):
            self.d = {(value,): 1}
        else:
            self.d = {(): value} if value else {}

    def __add__(self, q):
        q = q if isinstance(q, P) else P(q)
        out = self.d.copy()
        for k, v in q.d.items():
            out[k] = out.get(k, 0) + v
        return P(out)

    __radd__ = __add__

    def __neg__(self):
        return P({k: -v for k, v in self.d.items()})

    def __sub__(self, q):
        return self + -(q if isinstance(q, P) else P(q))

    def __rsub__(self, q):
        return -self + q

    def __mul__(self, q):
        q = q if isinstance(q, P) else P(q)
        out = {}
        for a, c in self.d.items():
            for b, d in q.d.items():
                k = tuple(sorted(a + b))
                out[k] = out.get(k, 0) + c * d
        return P(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        check(isinstance(n, int) and n >= 0, "Polynomial exponent")
        result = P(1)
        for _ in range(n):
            result = result * self
        return result

    def degree(self):
        return max(map(len, self.d), default=-1)

    def at(self, values):
        total = 0
        for monomial, coefficient in self.d.items():
            term = coefficient
            for name in monomial:
                term *= values[name]
            total += term
        return total


POS = "o w M g xp yp up vp sp tp qb qv J".split()
NAT = "dwb dwk dyk a1 a2 s1 s2 t1 t2 r1 r2".split()
EXPECTED_DEGREES = [4, 4, 4, 2, 2, 3, 2, 2, 1, 1, 1, 1, 6, 1, 2]


def power_residuals(c, p):
    o, w, m, g, x, y, u, v, s, t, qb, qv, j = (p[n] for n in POS)
    a, b = p["ap"] + 1, p["bp"] + 1
    z = {n: p[n] - 1 for n in NAT}
    return [x**2 - (a**2 - 1)*y**2 - 1,
            u**2 - (a**2 - 1)*v**2 - 1,
            s**2 - (b**2 - 1)*t**2 - 1,
            b - 4*y*qb - 1,
            b - a + u*(z["a1"] - z["a2"]),
            v - y**2*qv,
            s - x + u*(z["s1"] - z["s2"]),
            t - c + 4*y*(z["t1"] - z["t2"]),
            y - c - z["dyk"], w - 2 - z["dwb"],
            w - c - z["dwk"], m - 2*o - j,
            a**2 - ((w + 1)**2 - 1)*w**2*g**2 - 1,
            4*a - m - 5,
            x - y*(a - 2) - 2*o + m*(z["r1"] - z["r2"])]


class Formula:
    def __init__(self, edges, initial, halt, horizon, exact=False):
        self.variables = set()
        self.slots = []
        self.edges = edges
        self.horizon = horizon
        self.exact = exact

        def leaf(name):
            check(name not in self.variables, "Distinct leaf")
            self.variables.add(name)
            return P(name)

        def emit(label, residual):
            check(label not in {a for a, _ in self.slots}, "Distinct residual slot")
            self.slots.append((label, residual if isinstance(residual, P) else P(residual)))

        gaps = [leaf("gap" + str(i)) for i in range(3)]
        total = sum(gaps)
        aa, bb = leaf("A"), leaf("B")
        for label, counter, gap in (("left", aa, gaps[0]), ("right", bb, gaps[2])):
            local = {n: leaf(label + "." + n) for n in POS + ["ap", "bp"] + NAT}
            rr = power_residuals(counter, local)
            check(len(local) == 26, "26 leaves including output")
            check([p.degree() for p in rr] == EXPECTED_DEGREES, "Module residual degrees")
            for n, r in enumerate(rr, 1):
                emit(label + ".R" + str(n), r)
            emit(label + ".gap", (20*gap - total)*local["o"] - 2*total)
        if horizon == 0:
            emit("empty-trace", initial - halt)
        else:
            counters = [(aa, bb)] + [(leaf("A"+str(t)), leaf("B"+str(t)))
                                      for t in range(1, horizon+1)]
            select = [[leaf("select.%d.%d" % (t, e)) - 1 for e in range(len(edges))]
                      for t in range(horizon)]
            for t in range(horizon):
                row = select[t]
                for e, s in enumerate(row):
                    emit("boolean.%d.%d" % (t, e), s*(s - 1))
                emit("one.%d" % t, sum(row) - 1)
                for axis in range(2):
                    emit("update.%d.%d" % (t, axis), counters[t+1][axis] - counters[t][axis]
                         - sum(s*ed[axis+2] for s, ed in zip(row, edges)))
                for e, ed in enumerate(edges):
                    if ed[4] is not None:
                        emit("guard.%d.%d" % (t, e), row[e]*(counters[t][ed[4]] - 1))
            emit("source", sum(ed[0]*s for ed, s in zip(edges, select[0])) - initial)
            for t in range(horizon-1):
                emit("link.%d" % t, sum(ed[1]*s for ed, s in zip(edges, select[t]))
                     - sum(ed[0]*s for ed, s in zip(edges, select[t+1])))
            emit("target", sum(ed[1]*s for ed, s in zip(edges, select[-1])) - halt)
            if exact:
                hh = [i for i, ed in enumerate(edges) if ed == (halt, halt, 0, 0, None)]
                check(len(hh) == 1, "Unique padding edge")
                emit("no-early-halt", sum(row[hh[0]] for row in select))
        self.polynomial = sum((r*r for _, r in self.slots), P())


# Fresh finite instruction data, distinct from the candidate checker's graph.
# Tuple: source, target, increment A, increment B, zero-test axis (or None).
BRANCHES = [(10, 20, 0, 0, 0), (10, 30, -1, 0, None),
            (20, 40, 0, 1, None), (30, 40, 0, 0, 1),
            (30, 50, 0, -1, None), (40, 60, 1, 0, None),
            (50, 60, 0, 1, None), (60, 60, 0, 0, None)]


def ledger_checks():
    rows = []
    graphs = [("branching", BRANCHES, 10, 60),
              ("halt-only-zero-code", [(0, 0, 0, 0, None)], 0, 0),
              ("signed-state-codes", [(-3, 7, 1, 0, None), (7, 7, 0, 0, None)], -3, 7)]
    for name, edges, initial, halt in graphs:
        for horizon in (0, 1, 2, 3, 5):
            for exact in (False, True):
                f = Formula(edges, initial, halt, horizon, exact)
                e = len(edges)
                z = sum(ed[4] is not None for ed in edges)
                check(len(f.variables) == 57 + horizon*(e+2), "Variable count")
                check(len(f.slots) == 33 + horizon*(e+z+4) + int(exact and horizon > 0),
                      "Residual slot count")
                check(f.polynomial.degree() == 12, "Exact degree")
                top = {m: c for m, c in f.polynomial.d.items() if len(m) == 12}
                expected = {tuple(sorted([p+".w"]*8 + [p+".g"]*4)): 1 for p in ("left", "right")}
                check(top == expected, "Exact degree-twelve homogeneous part")
                support = {n for m in f.polynomial.d for n in m}
                check(support == f.variables, "All declared leaves used")
                rows.append({"graph": name, "T": horizon, "exact": exact,
                             "witnesses": len(f.variables)-3, "residual_slots": len(f.slots),
                             "nonzero_residual_polynomials": sum(bool(p.d) for _, p in f.slots),
                             "degree": 12, "expanded_terms": len(f.polynomial.d)})
    return rows


def pell_pair(parameter, index):
    # Independently written evaluation of (parameter + sqrt(parameter^2-1))^index.
    x, y = 1, 0
    for _ in range(index):
        x, y = parameter*x + (parameter*parameter-1)*y, x + parameter*y
    return x, y


def full_power_fixture(c):
    check(c in (1, 2), "Only declared small fixture indices")
    a, w, g, m, output = 17, 2, 3, 63, 2**(c-1)
    x, y = pell_pair(a, c)
    # Matiyasevic constructive witness index, evaluated only for c=1,2.
    n = 2*c*y
    u, v = pell_pair(a, n)
    modulus = 4*y
    check(gcd(u, modulus) == 1, "CRT fixture coprimality")
    b = a + u*((1-a)*pow(u, -1, modulus) % modulus)
    s, t = pell_pair(b, c)
    p = dict(zip(POS, [output, w, m, g, x, y, u, v, s, t,
                       (b-1)//modulus, v//(y*y), m-2*output]))
    p.update({"ap": a-1, "bp": b-1, "dwb": w-2+1, "dwk": w-c+1, "dyk": y-c+1})
    # Solve L + modulus*z1 - modulus*z2 = 0 with nonnegative z1,z2.
    for left, divisor, first, second in ((b-a, u, "a1", "a2"),
                                        (s-x, u, "s1", "s2"),
                                        (t-c, modulus, "t1", "t2"),
                                        (x-y*(a-2)-2*output, m, "r1", "r2")):
        check(left % divisor == 0, "Integral quotient fixture")
        q = left//divisor
        p[first], p[second] = max(-q, 0)+1, max(q, 0)+1
    check(set(p) == set(POS + ["ap", "bp"] + NAT), "Full 26-leaf fixture")
    check(min(p.values()) > 0, "Every POWER leaf positive")
    check(power_residuals(c, p) == [0]*15, "All fifteen POWER residuals")
    return p


def primitive(a, b):
    largest = max(a, b)
    left = 2**largest + 2**(largest-a+1)
    right = 2**largest + 2**(largest-b+1)
    middle = 20*2**largest - left - right
    factor = gcd(left, gcd(middle, right))
    return tuple(n//factor for n in (left, middle, right)), factor


def assign(f, a, b, path, counter_rows, power, scale=1):
    # path and counter_rows are literal independently declared algebra fixtures.
    check(len(path) == len(counter_rows) == f.horizon, "Fixture horizon")
    result = {"A": a+1, "B": b+1}
    gaps, _ = primitive(a, b)
    result.update({"gap"+str(i): scale*g for i, g in enumerate(gaps)})
    for prefix, c in (("left", a+1), ("right", b+1)):
        result.update({prefix+"."+n: v for n, v in power[c].items()})
    for t, selected in enumerate(path):
        result.update({"select.%d.%d" % (t, e): 1+int(e == selected) for e in range(len(f.edges))})
        result["A"+str(t+1)], result["B"+str(t+1)] = counter_rows[t]
    check(set(result) == f.variables and min(result.values()) > 0, "Full positive assignment")
    return result


def fixture_checks(power):
    count = 0
    fixtures = [(0, 0, [0, 2, 5], [(1, 1), (1, 2), (2, 2)]),
                (0, 1, [0, 2, 5], [(1, 2), (1, 3), (2, 3)]),
                (1, 0, [1, 3, 5], [(1, 1), (1, 1), (2, 1)]),
                (1, 1, [1, 4, 6], [(1, 2), (1, 1), (1, 2)])]
    for a, b, path, counters in fixtures:
        for padding in (0, 1, 3):
            horizon = 3+padding
            f = Formula(BRANCHES, 10, 60, horizon)
            for scale in (1, 13):
                val = assign(f, a, b, path+[7]*padding, counters+[counters[-1]]*padding, power, scale)
                check(all(r.at(val) == 0 for _, r in f.slots), "Full accepted fixture residuals")
                check(f.polynomial.at(val) == 0, "Expanded full polynomial fixture")
                exact = Formula(BRANCHES, 10, 60, horizon, True)
                check(exact.polynomial.at(val) == padding**2, "Exact-halt padding contribution")
                corrupt = val.copy()
                corrupt["A1"] += 1
                check(f.polynomial.at(corrupt) > 0, "Counter corruption detected")
                corrupt = val.copy()
                corrupt["gap0"] += 1
                check(f.polynomial.at(corrupt) > 0, "Input corruption detected")
                shifted = val.copy()
                for suffix in ("a1", "a2"):
                    shifted["left."+suffix] += 10**20
                check(f.polynomial.at(shifted) == 0, "Infinite-fiber common shift example")
                count += 1
    for initial in (60, 10):
        f = Formula(BRANCHES, initial, 60, 0)
        values = assign(f, 1, 0, [], [], power)
        check(f.polynomial.at(values) == (initial-60)**2, "T=0 semantics")
        count += 1
    halt = [(60, 60, 0, 0, None)]
    f = Formula(halt, 60, 60, 2)
    values = assign(f, 0, 0, [0, 0], [(1, 1), (1, 1)], power)
    check(f.polynomial.at(values) == 0, "Initially halted padded fixture")
    check(Formula(halt, 60, 60, 2, True).polynomial.at(values) == 4, "Initially halted exact rejection")
    # Directly verify the packet's smaller exponent-zero fixture as displayed.
    small = dict(zip(POS, [1, 2, 63, 3, 17, 1, 577, 34, 17, 1, 4, 34, 61]))
    small.update({"ap": 16, "bp": 16})
    small.update({n: 2 if n == "dwk" else 1 for n in NAT})
    check(power_residuals(1, small) == [0]*15 and min(small.values()) > 0,
          "Packet exponent-zero fixture")
    # Exact natural-subtraction translation, tested independently on a finite box.
    for u in range(80):
        for v in range(80):
            check((max(u-v, 0) == 1) == (u == v+1), "Truncated subtraction translation")
    return {"full_native_assignments": count+1, "exact_halt_and_corruption_checked": True,
            "packet_exponent_zero_fixture": True, "natural_subtraction_pairs": 6400,
            "module_fixtures": [{"C": c, "o": p["o"], "leaves": len(p),
                                 "largest_leaf_bits": max(v.bit_length() for v in p.values())}
                                for c, p in power.items()]}


def decode(g):
    total = sum(g)
    answer = []
    for endpoint in (g[0], g[2]):
        divisor = 20*endpoint-total
        if divisor <= 0:
            return None
        output, remainder = divmod(2*total, divisor)
        if remainder or output < 1 or output & (output-1):
            return None
        answer.append(output.bit_length()-1)
    return tuple(answer)


def normalization_checks():
    distribution = {}
    count = 0
    for a in range(129):
        for b in range(129):
            g, c = primitive(a, b)
            m = max(a, b)
            expected = (1 if m == 0 else 4 if a == b == 1 else 2 if m == 1
                        else 10 if a % 4 == b % 4 == 3 else 2)
            check(c == expected, "Exact primitive gcd")
            left = Fraction(1, 20) + Fraction(1, 10*2**a)
            right = Fraction(1, 20) + Fraction(1, 10*2**b)
            middle = 1-left-right
            minimum = lcm(left.denominator, middle.denominator, right.denominator)
            check(sum(g) == minimum, "Independent reduced-denominator minimum scale")
            check(tuple(int(x*minimum) for x in (left, middle, right)) == g, "Primitive triple")
            check(min(g) > 0 and g[1] == max(g) and gcd(g[0], gcd(g[1], g[2])) == 1,
                  "Positivity, largest gap, primitive gcd")
            bits = (5 if m == 0 else 4 if a == b == 1 else 5 if m == 1
                    else m+2 if c == 10 else m+4)
            check(minimum.bit_length() == bits, "Exact bit length")
            check(bits-1 <= max(x.bit_length() for x in g) <= bits, "Gap bit-height bracket")
            if m >= 2:
                check(2**(m+1) <= minimum <= 10*2**m, "Uniform scale bracket")
            for scale in (1, 3, 29):
                scaled = tuple(scale*n for n in g)
                check(decode(scaled) == (a, b), "Scaled decoder inverse")
                check(2**a <= 2*sum(scaled) and 2**b <= 2*sum(scaled), "Decoder output bound")
            distribution[str(c)] = distribution.get(str(c), 0)+1
            count += 1
    # Exhaustive positive integer inputs up to total 96. The expected set is
    # generated independently from reduced rational coordinates and their lcm.
    limit = 96
    expected_inputs = {}
    for a in range((2*limit).bit_length()):
        for b in range((2*limit).bit_length()):
            x, z = Fraction(1, 20)+Fraction(1, 10*2**a), Fraction(1, 20)+Fraction(1, 10*2**b)
            y = 1-x-z
            step = lcm(x.denominator, y.denominator, z.denominator)
            for total in range(step, limit+1, step):
                triple = tuple(int(q*total) for q in (x, y, z))
                check(triple not in expected_inputs, "Unique counters from shape")
                expected_inputs[triple] = (a, b)
    checked = 0
    for total in range(3, limit+1):
        for x in range(1, total-1):
            for y in range(1, total-x):
                triple = (x, y, total-x-y)
                check(decode(triple) == expected_inputs.get(triple), "Exhaustive native-input decoder")
                checked += 1
    return {"counter_range": [0, 128], "normalization_pairs": count,
            "scaled_decodings": 3*count, "gcd_distribution": distribution,
            "exhaustive_total_scale_bound": limit, "exhaustive_positive_triples": checked,
            "exhaustive_encoded_triples": len(expected_inputs)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    source, output = args.source.resolve(), args.output.resolve()
    check(source.is_dir(), "Source directory exists")
    check(not output.exists(), "Output must be a new external directory")
    check(output != source and source not in output.parents, "Output outside frozen source")
    check(output != Path(__file__).resolve().parent, "Output separate from checker")
    before = snapshot(source)
    binding = bind(source)
    ledger = ledger_checks()
    power = {c: full_power_fixture(c) for c in (1, 2)}
    fixtures = fixture_checks(power)
    normalization = normalization_checks()
    check(snapshot(source) == before, "Frozen source content, modes, sizes, mtimes preserved")
    receipt = {"status": "PASS", "checker_sha256": digest(Path(__file__).read_bytes()),
               "source_binding": binding, "ledger_instances": ledger,
               "fixtures": fixtures, "normalization": normalization,
               "source_snapshot": before, "source_unchanged": True,
               "execution_scope": "Only this independently authored standard-library checker; source files inert",
               "limits": "Finite support only. All-exponent adapter relies on pinned Pell theorems, no Lean build. Physical transport uses retained compiler theorem; no simulator or machine interpreter."}
    output.mkdir(parents=True)
    (output / "receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True)+"\n")
    (output / "power-fixtures.json").write_text(json.dumps({str(c): p for c, p in power.items()}, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"status": "PASS", "ledger_instances": len(ledger),
                      "full_native_assignments": fixtures["full_native_assignments"],
                      **normalization, "receipt": str(output / "receipt.json")}, sort_keys=True))


if __name__ == "__main__":
    main()
