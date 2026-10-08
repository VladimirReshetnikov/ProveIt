"""Exact certificates and finite-tail homology on binary signed braid runs.

This entry point never expands run exponents or constructs a PD diagram.
The signed Seifert tests are the maintained criteria evaluated on the braid
path graph. Remaining cases use the exact finite-tail macro homology backend.
"""
from __future__ import annotations

import argparse
from dataclasses import replace
import json
from pathlib import Path
import re
import sys
from time import monotonic

from .seifert import _summary
from .twist.core import Budget, ResourceLimit, Run, components, runs_from_word, validate_runs
from .twist.long_tail import tail_homology


def encoded_integer(value):
    """Read a JSON integer or an explicitly signed hexadecimal integer."""
    if type(value) is int:
        return value
    if isinstance(value, str) and re.fullmatch(r"[+-]?0[xX][0-9a-fA-F]+", value):
        return int(value, 16)
    raise ValueError("integer fields require integers or signed hexadecimal strings")


def load_braid(value):
    """Parse word/run JSON without converting a run to individual crossings."""
    if not isinstance(value, dict):
        raise ValueError("input must be a JSON object")
    data = value.get("braid", value)
    if not isinstance(data, dict) or "strands" not in data:
        raise ValueError("expected braid.strands; PD and grid inputs are not supported")
    strands = encoded_integer(data["strands"])
    if ("word" in data) == ("runs" in data):
        raise ValueError("provide exactly one of word or runs")
    if "word" in data:
        if not isinstance(data["word"], list):
            raise ValueError("word must be a list of signed generator indices")
        return strands, runs_from_word(strands, (encoded_integer(x) for x in data["word"]))
    if not isinstance(data["runs"], list) or any(
            not isinstance(run, list) or len(run) != 2 for run in data["runs"]):
        raise ValueError("runs must be [generator, signed_exponent] pairs")
    return strands, validate_runs(strands, (
        Run(encoded_integer(generator), encoded_integer(exponent))
        for generator, exponent in data["runs"]))


def json_safe(value):
    """Serialize very large integers in hex without relaxing Python safeguards."""
    if type(value) is int and value.bit_length() > 4096:
        return hex(value)
    if isinstance(value, dict):
        return {key: json_safe(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(item) for item in value]
    return value


def signed_run_seifert_data(strands, runs):
    """Compute production-convention Seifert counts without expanding runs."""
    runs = validate_runs(strands, runs)
    if components(strands, runs) != 1:
        raise ValueError("unknot recognition requires a one-component braid closure")
    positive = {run.generator for run in runs if run.exponent < 0}
    negative = {run.generator for run in runs if run.exponent > 0}
    # The maintained PD conversion reverses raw braid-generator signs.
    return _summary(sum(abs(run.exponent) for run in runs),
                    -sum(run.exponent for run in runs), strands,
                    strands - len(positive), strands - len(negative))


def signed_run_certificate(strands, runs):
    """Return an exact structural certificate or None when inconclusive."""
    data = signed_run_seifert_data(strands, runs)
    lower, upper = data["rasmussen_interval"]
    if data["canonical_genus"] == 0:
        status, criterion = "UNKNOT", "seifert-genus-zero"
    elif data["homogeneity_defect"] == 0:
        status, criterion = "KNOTTED", "homogeneous-seifert-genus"
    elif lower > 0 or upper < 0:
        status, criterion = "KNOTTED", "rasmussen-interval"
    else:
        return None
    return {"version": 1, "status": status, "criterion": criterion,
            "representation": "binary signed braid runs",
            "sign_convention": "production PD: writhe = -sum(run exponents)",
            **data}


def verify_signed_run_certificate(strands, runs, certificate):
    """Replay counts, accepting the numeric hex fields emitted by json_safe."""
    if not isinstance(certificate, dict) or type(certificate.get("version")) is not int:
        return False
    try:
        # Decode only the specified numeric fields. Text, version, and the
        # exact schema are still checked below; booleans are not integers.
        certificate = dict(certificate)
        for key in ("crossings", "writhe", "seifert_circles", "positive_components",
                    "negative_components", "homogeneity_defect", "canonical_genus"):
            certificate[key] = encoded_integer(certificate.get(key))
        interval = certificate.get("rasmussen_interval")
        if not isinstance(interval, list) or len(interval) != 2:
            return False
        certificate["rasmussen_interval"] = [encoded_integer(value) for value in interval]
        runs = validate_runs(strands, runs)
        # A knot must use every adjacent generator: avoid a huge allocation.
        if strands > len(runs) + 1:
            return False
        permutation = list(range(strands))
        occurrences = {}
        n = exponent = 0
        for run in runs:
            n += abs(run.exponent)
            exponent += run.exponent
            signs = occurrences.setdefault(run.generator, [False, False])
            signs[run.exponent > 0] = True
            if run.exponent & 1:
                i = run.generator - 1
                permutation[i], permutation[i + 1] = permutation[i + 1], permutation[i]
        visited = set()
        vertex = 0
        while vertex not in visited:
            visited.add(vertex)
            vertex = permutation[vertex]
        if len(visited) != strands:
            return False
        positive = strands - sum(values[0] for values in occurrences.values())
        negative = strands - sum(values[1] for values in occurrences.values())
        genus2 = n - strands + 1
        defect = strands + 1 - positive - negative
        lower = -exponent - strands + 2 * positive - 1
        upper = -exponent + strands - 2 * negative + 1
        if genus2 < 0 or genus2 & 1 or defect < 0:
            return False
        if genus2 == 0:
            status, criterion = "UNKNOT", "seifert-genus-zero"
        elif defect == 0:
            status, criterion = "KNOTTED", "homogeneous-seifert-genus"
        elif lower > 0 or upper < 0:
            status, criterion = "KNOTTED", "rasmussen-interval"
        else:
            return False
        expected = {
            "version": 1, "status": status, "criterion": criterion,
            "representation": "binary signed braid runs",
            "sign_convention": "production PD: writhe = -sum(run exponents)",
            "crossings": n, "writhe": -exponent, "seifert_circles": strands,
            "positive_components": positive, "negative_components": negative,
            "homogeneity_defect": defect, "canonical_genus": genus2 // 2,
            "rasmussen_interval": [lower, upper],
        }
        for key, value in expected.items():
            if type(value) is int and type(certificate.get(key)) is not int:
                return False
        interval = certificate.get("rasmussen_interval")
        if not isinstance(interval, list) or any(type(x) is not int for x in interval):
            return False
        return certificate == expected
    except (ValueError, TypeError, ArithmeticError, KeyError):
        return False


def recognize_runs(strands, runs, *, budget=None, check_d2=False,
                   use_structural=True, selected=None):
    """Exact run-input recognition, with UNKNOWN on a computational limit."""
    runs = validate_runs(strands, runs)
    if components(strands, runs) != 1:
        raise ValueError("unknot recognition requires a one-component braid closure")
    cap = replace(Budget() if budget is None else budget)
    if selected is not None and (type(selected) is not int or not 0 <= selected < len(runs)):
        raise ValueError("selected must be a valid zero-based run index")
    start = monotonic()
    deadline = None if cap.seconds is None else start + cap.seconds
    try:
        if deadline is not None and monotonic() >= deadline:
            raise ResourceLimit("time budget exhausted")
        if use_structural:
            certificate = signed_run_certificate(strands, runs)
            if deadline is not None and monotonic() >= deadline:
                raise ResourceLimit("time budget exhausted")
            if certificate is not None:
                return {"status": certificate["status"], "method": "signed-run-structural",
                        "certificate": certificate, "seconds": monotonic() - start}
        remaining = None if deadline is None else max(0.0, deadline - monotonic())
        result = tail_homology(strands, runs, selected=selected,
                               budget=replace(cap, seconds=remaining), check_d2=check_d2)
        return {"status": "UNKNOT" if result["reduced_rank"] == 1 else "KNOTTED",
                "method": "symbolic-twist-khovanov-F2", "homology": result,
                "seconds": monotonic() - start}
    except (ResourceLimit, MemoryError) as exc:
        return {"status": "UNKNOWN", "method": "resource-limit", "reason": str(exc),
                "seconds": monotonic() - start}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", help="JSON file, or - for standard input")
    parser.add_argument("--mode", choices=("recognize", "homology", "certificate"),
                        default="recognize")
    parser.add_argument("--selected-run", type=int)
    parser.add_argument("--no-structural", action="store_true")
    parser.add_argument("--check-d2", action="store_true")
    parser.add_argument("--seconds", type=float)
    for name, default in (("max-states", 250000), ("max-basis", 1000000),
                          ("max-matrix-bits", 1000000000), ("max-xors", 20000000)):
        parser.add_argument("--" + name, type=int, default=default)
    args = parser.parse_args(argv)
    try:
        value = json.load(sys.stdin) if args.input == "-" else json.loads(Path(args.input).read_text())
        strands, runs = load_braid(value)
        cap = Budget(args.max_states, args.max_basis, args.max_matrix_bits,
                     args.max_xors, args.seconds)
        if args.mode == "homology":
            result = tail_homology(strands, runs, selected=args.selected_run,
                                   budget=cap, check_d2=args.check_d2)
        elif args.mode == "certificate":
            if args.selected_run is not None or args.no_structural:
                raise ValueError("certificate mode does not accept tail selection or --no-structural")
            start = monotonic()
            if cap.seconds == 0:
                raise ResourceLimit("time budget exhausted")
            certificate = signed_run_certificate(strands, runs)
            if cap.seconds is not None and monotonic() - start >= cap.seconds:
                raise ResourceLimit("time budget exhausted")
            result = {"status": "INCONCLUSIVE" if certificate is None else certificate["status"],
                      "certificate": certificate}
        else:
            result = recognize_runs(strands, runs, selected=args.selected_run, budget=cap,
                                    check_d2=args.check_d2, use_structural=not args.no_structural)
    except (ValueError, TypeError, OSError) as exc:
        print(json.dumps({"status": "INVALID", "reason": str(exc)}))
        return 2
    except (ResourceLimit, MemoryError) as exc:
        print(json.dumps({"status": "UNKNOWN", "reason": str(exc)}))
        return 3
    print(json.dumps(json_safe(result), indent=2, sort_keys=True))
    return 3 if result.get("status") in ("UNKNOWN", "INCONCLUSIVE") else 0


if __name__ == "__main__":
    raise SystemExit(main())
