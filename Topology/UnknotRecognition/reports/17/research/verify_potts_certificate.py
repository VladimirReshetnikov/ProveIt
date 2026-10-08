"""Replay an exact q=6 Potts obstruction certificate.

This verifier validates its input independently of the report, but it REUSES
the production exact Potts algorithm. It is not an independent mathematical
implementation; check_potts_independent.py is the separate small-cube oracle.

Schema:
  {"schema": "fastunknot.potts-exact-certificate/v1", "pd": [...],
   "order": [...], "shade": 0, "input_sha256": "...", "evidence": {...}}

Evidence uses partition_function_hex and unknot_partition_hex, each a pair
of canonical signed hexadecimal strings (for example "0x0" or "-0x2a").
The draft v1 schema accepts either exact witness kind; it does not accept
decimal integer-pair evidence. Raw production evaluators still return ints.

The digest binds the explicit computation inputs against accidental changes;
it is not an authenticity signature. Every evidence field is recomputed.
Exit codes: 0 verified KNOTTED; 2 invalid certificate; 3 resource-limited
UNVERIFIED. Neither invalidity nor resource exhaustion is a knot verdict.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import importlib
import json
import math
from pathlib import Path
import sys
import time


SCHEMA = "fastunknot.potts-exact-certificate/v1"
KIND = "potts-jones-exact-differs-from-unknot"
FACTORIZED_KIND = "factorized-potts-jones-exact-differs-from-unknot"
KINDS = (KIND, FACTORIZED_KIND)
TOP_FIELDS = {"schema", "pd", "order", "shade", "input_sha256", "evidence"}


class InvalidCertificate(ValueError):
    """The purported certificate is malformed or fails exact replay."""


class UnverifiedCertificate(RuntimeError):
    """Replay exhausted its resources; the certificate remains unverified."""


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True, allow_nan=False)


def input_digest(pd, order, shade):
    encoded = canonical({"pd": pd, "order": order, "shade": shade, "q": 6})
    return hashlib.sha256(encoded.encode("ascii")).hexdigest()


def hexadecimal_pair(value, name):
    if type(value) is not list or len(value) != 2 or any(type(x) is not str for x in value):
        raise InvalidCertificate(name + " must contain two hexadecimal strings")
    result = []
    for coordinate in value:
        try:
            number = int(coordinate, 16)
        except ValueError as error:
            raise InvalidCertificate(name + " contains an invalid hexadecimal integer") from error
        if hex(number) != coordinate:
            raise InvalidCertificate(name + " is not canonical signed hexadecimal")
        result.append(number)
    return result


def make_certificate(pd, order, shade, evidence, *, fast_dir=None, kind=None):
    """Construct the envelope around a completed exact q6 obstruction.

    This helper does not certify correctness. verify_certificate performs the
    full replay. Use a supplied explicit shade; a heuristic shade=None cannot
    be bound reproducibly by this certificate schema.
    """
    pd = [list(row) for row in pd]
    order = list(order)
    evidence = copy.deepcopy(evidence)
    if type(evidence.get("q")) is not int or evidence["q"] != 6:
        raise InvalidCertificate("only a completed exact q=6 obstruction can be packaged")
    kind = kind or evidence.get("kind") or (
        FACTORIZED_KIND if "tensor_merges" in evidence else KIND)
    if kind not in KINDS:
        raise InvalidCertificate("unsupported exact witness kind")
    if "partition_function" in evidence or "unknot_partition" in evidence:
        _, _, _, to_witness = load_production(fast_dir, kind)
        evidence.pop("kind", None)
        evidence = to_witness(evidence, kind=kind)
        if evidence is None:
            raise InvalidCertificate("an inconclusive exact value cannot be packaged as an obstruction")
    elif (evidence.get("kind") != kind or evidence.get("differs") is not True
          or hexadecimal_pair(evidence.get("partition_function_hex"), "partition_function_hex")
          == hexadecimal_pair(evidence.get("unknot_partition_hex"), "unknot_partition_hex")):
        raise InvalidCertificate("not a completed hexadecimal exact obstruction")
    return {"schema": SCHEMA, "pd": pd, "order": order, "shade": shade,
            "input_sha256": input_digest(pd, order, shade), "evidence": evidence}


def load_production(fast_dir=None, kind=KIND):
    if fast_dir is None:
        root = Path(__file__).resolve().parents[1]
        candidates = (root / "fast", root / "work" / "fast")
        fast_dir = next((path for path in candidates
                         if (path / "fastunknot" / "potts_exact.py").is_file()), None)
        if fast_dir is None:
            raise InvalidCertificate("cannot find the exact backend; pass --fast-dir")
    fast_dir = Path(fast_dir).resolve()
    if not (fast_dir / "fastunknot" / "potts_exact.py").is_file():
        raise InvalidCertificate("--fast-dir does not contain fastunknot/potts_exact.py")
    sys.path.insert(0, str(fast_dir))
    package = importlib.import_module("fastunknot")
    if Path(package.__file__).resolve().parent != fast_dir / "fastunknot":
        raise InvalidCertificate("a different fastunknot checkout is already imported; use a fresh process")
    diagram_class = importlib.import_module("fastunknot.diagram").Diagram
    exact_module = importlib.import_module("fastunknot.potts_exact")
    exact = exact_module.potts_exact
    if kind == FACTORIZED_KIND:
        exact = importlib.import_module("fastunknot.potts_factorized_exact").factorized_potts_exact
    elif kind != KIND:
        raise InvalidCertificate("unsupported exact witness kind")
    limit = importlib.import_module("fastunknot.filters").FilterLimit
    return diagram_class, exact, limit, exact_module.witness_from_exact


def verify_certificate(certificate, *, fast_dir=None, max_states=200_000,
                       max_transitions=5_000_000, seconds=60.0):
    """Recompute the witness; a stored `differs` flag has no authority."""
    try:
        canonical(certificate)
    except (TypeError, ValueError) as error:
        raise InvalidCertificate("certificate contains a non-JSON value") from error
    if type(certificate) is not dict or set(certificate) != TOP_FIELDS:
        raise InvalidCertificate("unexpected or missing top-level fields")
    if certificate["schema"] != SCHEMA:
        raise InvalidCertificate("unsupported certificate schema")
    pd, order, shade = (certificate[key] for key in ("pd", "order", "shade"))
    if type(pd) is not list or any(type(row) is not list or len(row) != 4
                                  or any(type(x) is not int for x in row) for row in pd):
        raise InvalidCertificate("PD must be a list of four-integer crossing rows")
    if (type(order) is not list or any(type(x) is not int for x in order)
            or sorted(order) != list(range(len(pd)))):
        raise InvalidCertificate("order must be an explicit permutation of the crossings")
    if type(shade) is not int or shade not in (0, 1):
        raise InvalidCertificate("shade must be the explicit integer 0 or 1")
    digest = input_digest(pd, order, shade)
    if certificate["input_sha256"] != digest:
        raise InvalidCertificate("the computation-input digest does not match")
    evidence = certificate["evidence"]
    if type(evidence) is not dict or evidence.get("kind") not in KINDS:
        raise InvalidCertificate("not an exact Potts obstruction witness")
    if type(evidence.get("q")) is not int or evidence["q"] != 6:
        raise InvalidCertificate("this schema requires exact q=6 evidence")
    if "partition_function" in evidence or "unknot_partition" in evidence:
        raise InvalidCertificate("certificate evidence must use signed hexadecimal pairs")
    supplied_partition = hexadecimal_pair(evidence.get("partition_function_hex"),
                                          "partition_function_hex")
    supplied_expected = hexadecimal_pair(evidence.get("unknot_partition_hex"),
                                         "unknot_partition_hex")
    if seconds is not None and (type(seconds) not in (int, float) or seconds <= 0
                                or (type(seconds) is float and not math.isfinite(seconds))):
        raise InvalidCertificate("seconds must be positive and finite, or None")
    kind = evidence["kind"]
    Diagram, exact, FilterLimit, to_witness = load_production(fast_dir, kind)
    started = time.monotonic()

    def check():
        if seconds is not None and time.monotonic() - started >= seconds:
            raise UnverifiedCertificate("cooperative replay time budget exhausted")

    try:
        check()
        diagram = Diagram.from_pd(pd)
        check()
        fresh = exact(diagram, colors=6, order=order, shade=shade,
                      max_states=max_states, max_transitions=max_transitions,
                      check=check)
    except (FilterLimit, MemoryError) as error:
        raise UnverifiedCertificate(str(error) or "replay memory exhausted") from error
    except (ValueError, ArithmeticError) as error:
        raise InvalidCertificate("validated exact replay failed: " + str(error)) from error
    unequal = fresh["partition_function"] != fresh["unknot_partition"]
    if fresh["differs"] is not unequal:
        raise InvalidCertificate("the replay backend returned internally inconsistent evidence")
    if not unequal:
        raise InvalidCertificate("the exact value equals the unknot value; this is not an obstruction")
    if (supplied_partition != fresh["partition_function"]
            or supplied_expected != fresh["unknot_partition"]):
        raise InvalidCertificate("the exact hexadecimal integer pairs do not match replay")
    expected = to_witness(fresh, kind=kind)
    # Canonical JSON comparison also distinguishes booleans from integers.
    if canonical(evidence) != canonical(expected):
        wrong = sorted(key for key in set(evidence) | set(expected)
                       if key not in evidence or key not in expected
                       or canonical(evidence[key]) != canonical(expected[key]))
        raise InvalidCertificate("recomputed evidence differs in: " + ", ".join(wrong))
    return {"valid": True, "status": "KNOTTED", "q": 6,
            "crossing_count": diagram.crossings, "input_sha256": digest,
            "partition_function_hex": expected["partition_function_hex"],
            "unknot_partition_hex": expected["unknot_partition_hex"],
            "witness_kind": kind,
            "verification": "production exact algorithm replay",
            "independent_algorithm": False}


def self_test(fast_dir=None, large=False):
    Diagram, exact, _, to_witness = load_production(fast_dir)
    diagram = Diagram.from_braid(3, [1, -2, 1, -2])
    order, shade = list(range(diagram.crossings)), 0
    evidence = exact(diagram, colors=6, order=order, shade=shade,
                     max_states=None, max_transitions=None)
    certificate = make_certificate(diagram.pd, order, shade, evidence, fast_dir=fast_dir)
    verify_certificate(certificate, fast_dir=fast_dir)
    _, factored, _, _ = load_production(fast_dir, FACTORIZED_KIND)
    factored_evidence = factored(diagram, colors=6, order=order, shade=shade,
                                 max_states=None, max_transitions=None)
    factored_certificate = make_certificate(diagram.pd, order, shade, factored_evidence,
                                             fast_dir=fast_dir)
    verify_certificate(factored_certificate, fast_dir=fast_dir)
    from_witness = make_certificate(diagram.pd, order, shade,
                                    to_witness(evidence), fast_dir=fast_dir)
    assert from_witness == certificate
    mutations = []
    for field, value in (("differs", False), ("differs", 1), ("q", 5),
                         ("writhe", 100), ("kind", "forged"),
                         ("partition_function_hex", ["0x1", "0x0"]), ("peak_states", -1),
                         ("peak_states", float("nan"))):
        bad = copy.deepcopy(certificate)
        bad["evidence"][field] = value
        mutations.append(bad)
    bad = copy.deepcopy(certificate)
    bad["input_sha256"] = "0" * 64
    mutations.append(bad)
    for coordinate in ("0X1", "+0x1", "0x01", "-0x0", "1", "nan"):
        bad = copy.deepcopy(certificate)
        bad["evidence"]["partition_function_hex"][0] = coordinate
        mutations.append(bad)
    bad = copy.deepcopy(certificate)
    bad["evidence"]["partition_function"] = evidence["partition_function"]
    mutations.append(bad)
    bad = copy.deepcopy(factored_certificate)
    bad["evidence"]["tensor_merges"] += 1
    mutations.append(bad)
    bad = copy.deepcopy(certificate)
    bad["order"][0] = bad["order"][1]
    mutations.append(bad)
    bad = copy.deepcopy(certificate)
    bad["shade"] = True
    mutations.append(bad)
    bad = copy.deepcopy(certificate)
    bad["pd"][0][0] = True
    mutations.append(bad)
    bad = copy.deepcopy(certificate)
    unknot = Diagram.from_braid(2, [1])
    bad["pd"], bad["order"], bad["shade"] = [list(row) for row in unknot.pd], [0], 0
    bad["input_sha256"] = input_digest(bad["pd"], bad["order"], bad["shade"])
    mutations.append(bad)
    for i, bad in enumerate(mutations):
        try:
            verify_certificate(bad, fast_dir=fast_dir)
        except InvalidCertificate:
            pass
        else:
            raise AssertionError("tamper case accepted: " + str(i))
    try:
        verify_certificate(certificate, fast_dir=fast_dir, max_states=0)
    except UnverifiedCertificate:
        pass
    else:
        raise AssertionError("a resource-limited certificate was marked verified")
    # Verify serialization beyond Python's ordinary decimal-digit ceiling,
    # without changing that global setting. This synthetic envelope is not
    # represented as an actual knot certificate and is rejected on replay.
    original_limit = sys.get_int_max_str_digits() if hasattr(sys, "get_int_max_str_digits") else None
    huge_raw = copy.deepcopy(evidence)
    huge_raw["partition_function"] = [1 << 20_000, -(1 << 20_001)]
    huge_certificate = make_certificate(diagram.pd, order, shade, huge_raw, fast_dir=fast_dir)
    assert json.loads(canonical(huge_certificate)) == huge_certificate
    assert hexadecimal_pair(huge_certificate["evidence"]["partition_function_hex"],
                            "partition_function_hex") == huge_raw["partition_function"]
    try:
        verify_certificate(huge_certificate, fast_dir=fast_dir)
    except InvalidCertificate:
        pass
    else:
        raise AssertionError("a synthetic large pair was accepted as an actual knot value")
    if original_limit is not None:
        assert sys.get_int_max_str_digits() == original_limit
    large_record = None
    if large:
        long_diagram = Diagram.from_braid(3, [1, -2] * 6001)
        long_order = list(range(long_diagram.crossings))
        long_raw = factored(long_diagram, colors=6, order=long_order, shade=0,
                            max_states=None, max_transitions=None)
        largest_bits = max(abs(x).bit_length() for name in
                           ("partition_function", "unknot_partition") for x in long_raw[name])
        assert largest_bits > 15_000
        long_certificate = make_certificate(long_diagram.pd, long_order, 0, long_raw,
                                              fast_dir=fast_dir)
        decoded = json.loads(canonical(long_certificate))
        verify_certificate(decoded, fast_dir=fast_dir)
        large_record = {"crossings": long_diagram.crossings, "largest_pair_bits": largest_bits,
                        "status": "VERIFIED", "kind": FACTORIZED_KIND}
        if original_limit is not None:
            assert sys.get_int_max_str_digits() == original_limit
    return {"status": "PASS", "valid_certificates": 2,
            "rejected_tamper_cases": len(mutations), "resource_checks": 1,
            "synthetic_large_hex_roundtrips": 1, "synthetic_large_forgery_rejected": 1,
            "large_real_certificate": large_record,
            "independent_algorithm": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path)
    parser.add_argument("--fast-dir", type=Path)
    parser.add_argument("--max-states", type=int, default=200_000)
    parser.add_argument("--max-transitions", type=int, default=5_000_000)
    parser.add_argument("--seconds", type=float, default=60.0)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--large-self-test", action="store_true",
                        help="also replay a real 12002-crossing bounded-frontier certificate")
    args = parser.parse_args()
    try:
        if args.self_test or args.large_self_test:
            result = self_test(args.fast_dir, large=args.large_self_test)
        else:
            if args.certificate is None:
                raise InvalidCertificate("a certificate path is required")
            certificate = json.loads(args.certificate.read_text())
            result = verify_certificate(certificate, fast_dir=args.fast_dir,
                                        max_states=args.max_states,
                                        max_transitions=args.max_transitions,
                                        seconds=args.seconds)
    except UnverifiedCertificate as error:
        print(json.dumps({"valid": None, "status": "UNVERIFIED", "reason": str(error)}))
        return 3
    except (InvalidCertificate, OSError, json.JSONDecodeError) as error:
        print(json.dumps({"valid": False, "status": "INVALID", "reason": str(error)}))
        return 2
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
