#!/usr/bin/env python3
"""Audit an abstract lexicographic rollback budget; no topology is implemented.

Digits have radices r_1,...,r_L >= 1.  A strict decrease whose first changed
digit is j (one-based) receives charge L-j+1; initial construction receives L.
The exact maximum over every decreasing trace is sum(prod(r[:i]), i=1..L).

The auditor independently solves a maximum-weight path problem on the complete
lexicographic DAG.  This implicitly checks every strict decreasing sequence,
including those that skip states.  For very small state spaces it also explicitly
enumerates every nonempty decreasing sequence.  These are finite checks of the
combinatorial statement, not a proof of a geometric unknot-recognition backend.

Examples:
  python tools/hierarchy_budget.py --radices 3,1,2 --output data/budget.json
  python tools/hierarchy_budget.py --self-test --output data/budget_audit.json

Only the Python standard library is used.  The mathematical proof is in the
accompanying article; this program has quadratic audit cost in the number of
mixed-radix states and is intentionally unsuitable for large budgets.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path


def validate_radices(radices):
    """Return a tuple of positive integer radices, allowing the empty tuple."""
    radices = tuple(radices)
    if any(type(r) is not int or r < 1 for r in radices):
        raise ValueError("every radix must be a positive integer")
    return radices


def prefix_budget(radices):
    """The theorem's proposed sharp upper bound, including initial work."""
    radices = validate_radices(radices)
    prefix, prefixes = 1, []
    for r in radices:
        prefix *= r
        prefixes.append(prefix)
    return sum(prefixes), prefixes


def lex_rank(digits, radices):
    """Evaluate digits as a mixed-radix number with the first digit largest."""
    radices = validate_radices(radices)
    digits = tuple(digits)
    if len(digits) != len(radices):
        raise ValueError("digit and radix lengths differ")
    rank = 0
    for digit, radix in zip(digits, radices):
        if type(digit) is not int or not 0 <= digit < radix:
            raise ValueError("digit outside its radix")
        rank = rank * radix + digit
    return rank


def suffix_charge(high, low):
    """Charge a strict lexicographic decrease directly from its two vectors."""
    if len(high) != len(low) or not high > low:
        raise ValueError("a transition must be a strict lexicographic decrease")
    for index, (a, b) in enumerate(zip(high, low)):
        if a != b:
            if a <= b:
                raise AssertionError("the first changed digit did not decrease")
            return len(high) - index
    raise AssertionError("distinct vectors have no first difference")


def explicit_sequence_maximum(states):
    """Check every nonempty decreasing sequence by enumerating its state set."""
    length = len(states[0])
    best, checked = length, 0
    for mask in range(1, 1 << len(states)):
        trace = [i for i in range(len(states) - 1, -1, -1) if mask >> i & 1]
        score = length + sum(suffix_charge(states[a], states[b])
                             for a, b in zip(trace, trace[1:]))
        best = max(best, score)
        checked += 1
    return best, checked


def audit(radices, *, max_states=4096, explicit_states=10):
    """Compute a longest path over *all* strict lexicographic transitions.

    ``best[i]`` is the greatest subsequent charge attainable from state i.
    Every possible next state is considered.  Thus the dynamic program is
    independent of the odometer proof and does not assume adjacent transitions.
    """
    radices = validate_radices(radices)
    count = math.prod(radices)
    if count > max_states:
        raise ValueError(f"{count} states exceeds audit limit {max_states}")
    states = list(itertools.product(*(range(r) for r in radices)))
    length = len(radices)
    expected, prefixes = prefix_budget(radices)
    for index, state in enumerate(states):
        if lex_rank(state, radices) != index:
            raise AssertionError("mixed-radix rank is not lexicographic order")

    best, predecessor = [0] * count, [None] * count
    transitions = 0
    for high in range(count):
        for low in range(high):
            candidate = suffix_charge(states[high], states[low]) + best[low]
            transitions += 1
            if candidate > best[high]:
                best[high], predecessor[high] = candidate, low
    observed = length + max(best)
    odometer = length + sum(suffix_charge(states[i], states[i - 1])
                            for i in range(1, count))
    if observed != expected or odometer != expected:
        raise AssertionError((radices, expected, observed, odometer))

    # A maximizer can always be started at the largest vector.  Verify it;
    # this is an outcome of the DAG computation, not an assumption in max().
    if best[-1] != max(best):
        raise AssertionError("the largest state failed to maximize charge")
    path, cursor = [], count - 1
    while cursor is not None:
        path.append(cursor)
        cursor = predecessor[cursor]

    result = {
        "radices": list(radices),
        "length": length,
        "states": count,
        "prefix_products": prefixes,
        "predicted_maximum_including_initial": expected,
        "dynamic_program_maximum_including_initial": observed,
        "full_odometer_charge_including_initial": odometer,
        "strict_decreasing_transitions_checked": transitions,
        "maximizing_trace_ranks": path,
        "all_radices_at_least_two": all(r >= 2 for r in radices),
        "scope": "abstract charged level visits; no geometric backend",
        "passed": True,
    }
    if count <= explicit_states:
        explicit, sequences = explicit_sequence_maximum(states)
        if explicit != expected:
            raise AssertionError((radices, "explicit sequence maximum", explicit))
        result["explicit_nonempty_decreasing_sequences_checked"] = sequences
        result["explicit_sequence_maximum_including_initial"] = explicit
    if all(r >= 2 for r in radices) and not expected < 2 * count:
        raise AssertionError("geometric-sum consequence failed")
    return result


def self_test(*, max_length=5, max_radix=3, max_states=4096):
    """Audit all radix tuples in the specified finite box, including radix 1."""
    if max_length < 0 or max_radix < 1:
        raise ValueError("max length must be nonnegative and max radix positive")
    rows = []
    for length in range(max_length + 1):
        for radices in itertools.product(range(1, max_radix + 1), repeat=length):
            rows.append(audit(radices, max_states=max_states))
    return {
        "audit": "exhaustive small mixed-radix maximum-weight-path verification",
        "max_length": max_length,
        "max_radix": max_radix,
        "radix_tuples_checked": len(rows),
        "strict_decreasing_transitions_checked": sum(
            row["strict_decreasing_transitions_checked"] for row in rows),
        "explicit_nonempty_decreasing_sequences_checked": sum(
            row.get("explicit_nonempty_decreasing_sequences_checked", 0)
            for row in rows),
        "all_passed": all(row["passed"] for row in rows),
        "scope": "finite audits of a combinatorial theorem; not a topology solver",
        "cases": rows,
    }


def parse_radices(text):
    if not text.strip():
        return ()
    try:
        return validate_radices(int(value.strip()) for value in text.split(","))
    except ValueError as error:
        raise argparse.ArgumentTypeError(str(error)) from error


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--radices", type=parse_radices, default=None,
                      help="comma-separated positive radices, e.g. 3,1,2")
    mode.add_argument("--self-test", action="store_true",
                      help="audit every tuple of small radices")
    parser.add_argument("--max-length", type=int, default=5)
    parser.add_argument("--max-radix", type=int, default=3)
    parser.add_argument("--max-states", type=int, default=4096,
                        help="reject any individual DAG exceeding this size")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        if args.self_test:
            result = self_test(max_length=args.max_length,
                               max_radix=args.max_radix,
                               max_states=args.max_states)
        else:
            radices = args.radices if args.radices is not None else (3, 1, 2)
            result = audit(radices, max_states=args.max_states)
    except ValueError as error:
        parser.error(str(error))
    serialized = json.dumps(result, indent=2) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized)
        print(f"Wrote {args.output}")
    else:
        print(serialized, end="")


if __name__ == "__main__":
    main()
