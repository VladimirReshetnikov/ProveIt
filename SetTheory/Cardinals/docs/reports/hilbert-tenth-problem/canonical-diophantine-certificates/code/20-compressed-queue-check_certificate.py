"""Independent checker for exported fifo-quartic-v1 polynomials.

This deliberately does not import the compiler. It checks exact polynomial
identity (Q = sum residual**2), degree bounds, and the supplied natural zero.
It does not itself prove that the polynomial encodes the claimed queue run.
Usage: python code/check_certificate.py data/example_quartic.json [...]
"""
from __future__ import annotations
from pathlib import Path
import json
import sys


def integer(value: object) -> int:
    if type(value) is int:
        return value
    if isinstance(value, str) and (value.startswith("0x") or value.startswith("-0x")):
        return int(value, 16)
    raise ValueError("integer must be a JSON integer or an explicitly prefixed hex string")


def polynomial(records: list[dict], n: int) -> dict[tuple[int, ...], int]:
    result: dict[tuple[int, ...], int] = {}
    for term in records:
        coefficient = integer(term["coefficient"])
        indices = term["variables"]
        if not isinstance(indices, list) or any(type(i) is not int or not 0 <= i < n for i in indices):
            raise ValueError("invalid monomial variable index")
        monomial = tuple(sorted(indices))
        result[monomial] = result.get(monomial, 0) + coefficient
    return {m: c for m, c in result.items() if c}


def evaluate(poly: dict[tuple[int, ...], int], witness: list[int]) -> int:
    total = 0
    for monomial, coefficient in poly.items():
        term = coefficient
        for index in monomial:
            term *= witness[index]
        total += term
    return total


def check_file(path: Path) -> dict:
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("format") != "fifo-quartic-v1":
        raise ValueError("unrecognized certificate format")
    names = data["variables"]
    if any(not isinstance(name, str) for name in names) or len(set(names)) != len(names):
        raise ValueError("variable names must be distinct strings")
    n = len(names)
    residuals = [polynomial(p, n) for p in data["residuals"]]
    q = polynomial(data["polynomial"], n)
    if any(len(m) > 2 for p in residuals for m in p) or any(len(m) > 4 for m in q):
        raise ValueError("degree bound violated")
    expected: dict[tuple[int, ...], int] = {}
    for p in residuals:
        for m, c in p.items():
            for m2, c2 in p.items():
                term = tuple(sorted(m+m2))
                expected[term] = expected.get(term, 0) + c*c2
    expected = {m: c for m, c in expected.items() if c}
    if q != expected:
        raise ValueError("exported polynomial is not exactly the sum of residual squares")
    degree = max(map(len, q), default=0)
    if integer(data["degree"]) != degree:
        raise ValueError("incorrect exported degree metadata")
    witness = [integer(x) for x in data["witness"]]
    if len(witness) != n or any(x < 0 for x in witness):
        raise ValueError("witness must contain one natural number per variable")
    if any(evaluate(p, witness) != 0 for p in residuals) or evaluate(q, witness) != 0:
        raise ValueError("the supplied witness is not a zero")
    return {"file": path.name, "status": "PASS", "variables": n,
            "residuals": len(residuals), "degree": degree, "monomials": len(q)}


def main() -> None:
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    try:
        results = [check_file(Path(name)) for name in sys.argv[1:]]
    except (OSError, ValueError, TypeError, KeyError) as exc:
        raise SystemExit(f"FAIL: {exc}") from exc
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
