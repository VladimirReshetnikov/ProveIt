"""Reconstruct both V-weight circuits and certify their operation counts and exact degrees."""

import argparse
from collections import Counter
import gzip
from hashlib import sha256
import json
from pathlib import Path
import runpy

PARENT = Path(__file__).resolve().parent.parent / "ten-positive-index-weight"
BFS = PARENT.parents[1] / "candidates/one-page-ordinary13/coefficients"
MODULUS = 65537
PARENTS = {
    "zero98": "bd7ae70e69288cb035f24a564f99e9ea4282b5f647558e52ad34170f73795f82",
    "direct103": "42e3cfdb31d3ca792b3956085104ebcefd84490df6a51e7b424cdf76651c4439",
}
BFS_K_HASH = "4364134a56b54cf132beeb9acd8e832be68f9083f4359ace4a588a1ea76a60f7"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def weights(parent, bfs):
    folder = BFS if bfs else PARENT / "coefficients"
    values = {}
    for name, record in parent["coefficient_binding"]["ports"].items():
        data = gzip.decompress((folder / record["file"]).read_bytes())
        expected = BFS_K_HASH if bfs and name == "K0" else record["raw_sha256"]
        require(sha256(data).hexdigest() == expected, f"coefficient mismatch for {name}")
        values[name] = int.from_bytes(data, "little") % MODULUS
    return values


def rebind(rows):
    by_name = {row[0]: row[1:] for row in rows}
    require(by_name["kI"] == ["*", "k", "I"] and by_name["L"] == ["+", "kI", "cTR"],
            "unexpected weight definition")
    require(by_name["LB"][:2] == ["*", "L"], "unexpected transport product")
    return [[name, op, "V" if name == "LB" else left, right]
            for name, op, left, right in rows if name not in {"kI", "L"}]


def degree_certificate(rows, witnesses, constants):
    # Track a total-degree upper bound and its coefficient on the line
    # J=i=Y=eta=w (or x)=t, with the other witnesses zero, modulo MODULUS.
    # A nonzero leading coefficient witnesses the global lower bound.
    values = {s: (1, int(s in {"J", "i", "Y", "eta", "w", "x"})) for s in witnesses}
    values.update({s: (0, n) for s, n in constants.items()})

    def operand(x):
        return (0, x) if isinstance(x, int) else values[x]

    for name, op, left, right in rows:
        require(name not in values, f"redefined {name}")
        a, ca = operand(left)
        b, cb = operand(right)
        if op == "*":
            degree, coeff = a + b, ca * cb
        else:
            require(op in {"+", "-"}, f"unknown operation {op}")
            degree = max(a, b)
            coeff = (ca if a == degree else 0) + (1 if op == "+" else -1) * (cb if b == degree else 0)
        values[name] = (degree, coeff % MODULUS)
    return values["N"]


def verify(name, emit):
    raw = (PARENT / (name + ".json")).read_bytes()
    require(sha256(raw).hexdigest() == PARENTS[name], "parent graph hash mismatch")
    parent = json.loads(raw)
    rows = rebind(parent["source"])
    needed = {"N"}
    for register, _, left, right in reversed(rows):
        require(register in needed, f"dead register {register}")
        needed.update([left, right])
    # Compare the complete norm polynomial at the four ports to the parent's
    # independently expanded norm, including coefficients which could cancel.
    algebra = runpy.run_path(str(PARENT / "check.py"))
    ports = ("fs", "fa", "fb", "fc")
    norm = algebra["F8"](*(algebra["V"](port) for port in ports))
    require(len(norm) == 35 and algebra["cut"](rows, "N", ports) == norm, "norm mismatch")
    expected_count, expected_degree = (96, 432) if name == "zero98" else (101, 400)
    require(len(rows) == expected_count, "unexpected live operation count")
    leading = {}
    for label, bfs in [("original", False), ("BFS", True)]:
        degree, coeff = degree_certificate(rows, parent["witnesses"], weights(parent, bfs))
        require(degree == expected_degree and coeff != 0, f"degree certificate failed for {label}")
        leading[label] = coeff
    result = {"operations": len(rows), "breakdown": dict(Counter(row[1] for row in rows)),
              "degree": expected_degree, "leading_coefficients_mod_65537": leading}
    if emit:
        result.update(witnesses=parent["witnesses"], fixed_ports=parent["fixed_numerals"], source=rows)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", action="store_true", help="print every row of both verified circuits")
    args = parser.parse_args()
    print(json.dumps({n: verify(n, args.source) for n in PARENTS}, indent=2))
