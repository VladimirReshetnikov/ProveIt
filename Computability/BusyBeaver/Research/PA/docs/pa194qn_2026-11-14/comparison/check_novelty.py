#!/usr/bin/env python3
"""Compare candidates with the frozen current corpus, ignoring state names.

By default this also allows a different spanning start, tape reflection,
global binary-symbol complementation, and arbitrary terminal-write/move
effects. Bit complementation is a deliberately stronger structural test;
it is not asserted to preserve a zero-blank computation.
"""
import argparse
import hashlib
import json
from pathlib import Path
from graph_tools import parse, rooted, variants, fingerprint

_fingerprint_cache = {}


def check(candidate, corpus, strict_terminal=False):
    candidate = Path(candidate)
    corpus = Path(corpus)
    data = candidate.read_bytes()
    rows, states, declared, halts = parse(data)
    if len(halts) != 1:
        raise ValueError("candidate must have one terminal halt label")
    start = declared if declared is not None else (0 if 0 in states else None)
    if start is None:
        raise ValueError("declare the candidate start using '#! start N'")
    if rooted(rows, states, start)[1] != len(states):
        raise ValueError("candidate must be graph-reachable from its designated start")
    index = json.loads((corpus / "table_index.json").read_text())
    key = "table_class" if strict_terminal else "terminal_normalized_class"
    trial = variants(data, loose=not strict_terminal)
    matches = []
    eligible = [x for x in index if x["working_states"] == len(states) and
                x["max_reachable"] == len(states) and x["halt_count"] == 1]
    for x in eligible:
        # Reparse the bundled literal representative rather than trusting the
        # index's cached fingerprint. Cache across candidates in this process.
        literal = (corpus / x['table_file']).read_bytes()
        digest = hashlib.sha256(literal).hexdigest()
        if digest != x['sha256']:
            raise ValueError('corpus representative hash mismatch: ' + x['table_file'])
        cache_key = digest, strict_terminal
        if cache_key not in _fingerprint_cache:
            r, s, _declared, _halts = parse(literal)
            if len(s) != x['working_states'] or len(_halts) != 1:
                raise ValueError('corpus representative count mismatch: ' + x['table_file'])
            h, reached = fingerprint(r, s, loose=not strict_terminal)
            if reached != len(s) or (x.get(key) is not None and x[key] != h):
                raise ValueError('corpus representative fingerprint mismatch: ' + x['table_file'])
            _fingerprint_cache[cache_key] = h
        comparison_key = _fingerprint_cache[cache_key]
        for v in trial:
            if comparison_key == v["fingerprint"]:
                matches.append({"table_file": x["table_file"],
                                "source_locator": x["source_locator"], **v})
    return {"candidate": str(candidate), "candidate_sha256": hashlib.sha256(data).hexdigest(),
            "working_states": len(states), "transitions": len(rows), "start": start,
            "halt": next(iter(halts)), "corpus_tables": len(index),
            "same_size_spanning_tables": len(eligible),
            "literal_representatives_reparsed_and_hash_checked": len(eligible),
            "snapshot": "2337ce611a26e308697ccbddb2a1636f989f01c3",
            "allow_any_spanning_root": True, "allow_reflection": True,
            "allow_symbol_complementation": True,
            "ignore_terminal_write_and_direction": not strict_terminal,
            "variants": trial, "matches": matches, "structurally_new_in_corpus": not matches,
            "scope": "Structural comparison only; no halting, consistency, or global-priority conclusion."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidates", nargs="+", type=Path)
    parser.add_argument("--corpus", type=Path, default=Path(__file__).parent)
    parser.add_argument("--strict-terminal", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    results = [check(p, args.corpus, args.strict_terminal) for p in args.candidates]
    text = json.dumps(results, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text)
