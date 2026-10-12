"""Independent integer-only verifier for bundle quotient certificates.

The verifier never calls the producer, performs Gaussian elimination, or
imports Fraction.  It checks a supplied finite chain-pair fragment and an
exact primal or dual identity.  Geometric authentication is external.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys


INPUT_SCHEMA = "relative-chain-pair-v1"
CERT_SCHEMA = "relative-quotient-certificate-v1"
INPUT_KEYS = {"schema", "dims", "d2", "d3", "e2", "j1", "j2", "s"}
DIM_KEYS = {"c1", "c2", "c3", "e1", "e2"}


class VerificationError(ValueError):
    """An input contract or certificate identity is invalid."""


def _integer(value: object, name: str, minimum: int | None = None) -> int:
    if type(value) is not int:
        raise VerificationError(f"{name} must be a strict integer")
    if minimum is not None and value < minimum:
        raise VerificationError(f"{name} must be at least {minimum}")
    return value


def _vector(value: object, size: int, name: str) -> list[int]:
    if type(value) is not list or len(value) != size:
        raise VerificationError(f"{name} must be a list of length {size}")
    return [_integer(entry, f"{name}[{i}]") for i, entry in enumerate(value)]


def _matrix(value: object, rows: int, cols: int, name: str) -> list[list[int]]:
    if type(value) is not list or len(value) != rows:
        raise VerificationError(f"{name} must have {rows} rows")
    return [_vector(row, cols, f"{name}[{i}]") for i, row in enumerate(value)]


def _product(a: list[list[int]], b: list[list[int]], cols: int) -> list[list[int]]:
    """Multiply already shape-checked matrices, retaining empty dimensions."""
    return [
        [sum(row[k] * b[k][j] for k in range(len(row))) for j in range(cols)]
        for row in a
    ]


def _row_product(row: list[int], matrix: list[list[int]], cols: int) -> list[int]:
    return [sum(row[i] * matrix[i][j] for i in range(len(row))) for j in range(cols)]


def validate_input(data: object) -> dict[str, int]:
    """Validate dimensions, strict integers, and the three chain identities.

    The matrices describe d2:C2->C1, d3:C3->C2, e2:E2->E1,
    j1:E1->C1 and j2:E2->C2.  No manifold recognition is performed.
    """
    if type(data) is not dict or set(data) != INPUT_KEYS:
        raise VerificationError(f"input keys must be exactly {sorted(INPUT_KEYS)}")
    if data["schema"] != INPUT_SCHEMA:
        raise VerificationError("unsupported input schema")
    dims = data["dims"]
    if type(dims) is not dict or set(dims) != DIM_KEYS:
        raise VerificationError(f"dimension keys must be exactly {sorted(DIM_KEYS)}")
    dims = {name: _integer(dims[name], f"dims.{name}", 0) for name in DIM_KEYS}
    c1, c2, c3, e1, e2 = (dims[name] for name in ("c1", "c2", "c3", "e1", "e2"))
    d2 = _matrix(data["d2"], c1, c2, "d2")
    d3 = _matrix(data["d3"], c2, c3, "d3")
    delta2 = _matrix(data["e2"], e1, e2, "e2")
    j1 = _matrix(data["j1"], c1, e1, "j1")
    j2 = _matrix(data["j2"], c2, e2, "j2")
    s = _vector(data["s"], c2, "s")
    if _product(d2, d3, c3) != [[0] * c3 for _ in range(c1)]:
        raise VerificationError("chain identity d2*d3=0 fails")
    if _product(d2, j2, e2) != _product(j1, delta2, e2):
        raise VerificationError("chain-map identity d2*j2=j1*e2 fails")
    if any(sum(row[k] * s[k] for k in range(c2)) != 0 for row in d2):
        raise VerificationError("candidate is not a relative cycle: d2*s != 0")
    return dims


def input_digest(data: dict) -> str:
    """Bind a certificate to this exact JSON-compatible matrix instance."""
    encoded = json.dumps(data, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def verify(data: object, certificate: object) -> str:
    """Return the algebraic verdict or raise VerificationError.

    OUTSIDE_BUNDLE_IMAGE gives a strict q-progress statement only after a
    separate geometric wrapper authenticates the manifold, bundle, normal
    surface, orientation, admissibility and raw-cut conventions.
    """
    dims = validate_input(data)
    if type(certificate) is not dict:
        raise VerificationError("certificate must be an object")
    kind = certificate.get("kind")
    base_keys = {"schema", "input_sha256", "kind", "q"}
    if kind == "supported":
        expected = base_keys | {"a", "b"}
    elif kind == "outside":
        expected = base_keys | {"Y", "U"}
    else:
        raise VerificationError("certificate kind must be supported or outside")
    if set(certificate) != expected:
        raise VerificationError(f"certificate keys must be exactly {sorted(expected)}")
    if certificate["schema"] != CERT_SCHEMA:
        raise VerificationError("unsupported certificate schema")
    if certificate["input_sha256"] != input_digest(data):
        raise VerificationError("certificate is bound to a different input")
    q = _integer(certificate["q"], "q", 1)
    c2, c3, e1, e2 = (dims[name] for name in ("c2", "c3", "e1", "e2"))
    d3, delta2, j2, s = (data[name] for name in ("d3", "e2", "j2", "s"))
    if kind == "supported":
        a = _vector(certificate["a"], c3, "a")
        b = _vector(certificate["b"], e2, "b")
        for i in range(c2):
            value = sum(d3[i][k] * a[k] for k in range(c3))
            value += sum(j2[i][k] * b[k] for k in range(e2))
            if value != q * s[i]:
                raise VerificationError("support identity q*s=d3*a+j2*b fails")
        if any(sum(row[k] * b[k] for k in range(e2)) != 0 for row in delta2):
            raise VerificationError("bundle-chain identity e2*b=0 fails")
        return "INSIDE_BUNDLE_IMAGE"
    y = _vector(certificate["Y"], c2, "Y")
    u = _vector(certificate["U"], e1, "U")
    if _row_product(y, d3, c3) != [0] * c3:
        raise VerificationError("dual identity Y*d3=0 fails")
    if _row_product(y, j2, e2) != _row_product(u, delta2, e2):
        raise VerificationError("dual restriction identity Y*j2=U*e2 fails")
    if sum(y[i] * s[i] for i in range(c2)) != q:
        raise VerificationError("dual evaluation identity Y*s=q fails")
    return "OUTSIDE_BUNDLE_IMAGE"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args(argv)
    try:
        data = json.loads(args.input.read_text(encoding="utf-8"))
        certificate = json.loads(args.certificate.read_text(encoding="utf-8"))
        verdict = verify(data, certificate)
    except (OSError, ValueError) as error:
        print(f"verification failed: {error}", file=sys.stderr)
        return 2
    print(json.dumps({"valid": True, "verdict": verdict}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
