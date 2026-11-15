#!/usr/bin/env python3
"""Portable exact graph comparison against the packaged pinned PA corpus.

Only the Python standard library and ../comparison/census.py are required.
The candidate is compared with every spanning root of every frontier table.
The enlarged comparison permits control renaming, reflection, global symbol
exchange, and erased halt-entry actions. Symbol exchange is used only for
structural comparison, not as a blank-zero execution equivalence.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('pa194_census', ROOT/'comparison'/'census.py')
C = importlib.util.module_from_spec(spec)
spec.loader.exec_module(C)
EXPECTED_SHA256 = '64ac4ba569b770688a39a1545d5536ad631d15dbb756a0584a8956a83943b3a8'
EXPECTED_FRONTIER_MANIFEST = '3921edd03d5242b1b811c7abeddef7d0403eb05315a027fa23c84f0ad4793346'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def strong(rows, states):
    values = [C.canonical(rows, states, mirror=mirror, flip=flip, loose=True)
              for mirror in (False, True) for flip in (False, True)]
    require(all(v is not None for v in values), 'table has no spanning root')
    return min(values)


def digest(value):
    return hashlib.sha256(C.encode(value)).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=ROOT/'verification'/'novelty_check.json')
    args = ap.parse_args()
    candidate = ROOT/'machine'/'machine.tm'
    data = candidate.read_bytes()
    require(C.sha(data) == EXPECTED_SHA256, 'candidate bytes differ from the pinned release table')
    rows, states, declared = C.parse(data)
    require(states == list(range(194)), 'candidate must have dense working states 0..193')
    require(declared in (None, 0), 'candidate declares the wrong start')
    require({n for w, d, n in rows.values()} - set(states) == {194}, 'wrong halt label')
    rooted, reachable = C.traverse(rows, states, 0)
    require(reachable == 194, 'candidate does not have all 194 controls graph-reachable from start0')
    strict = C.canonical(rows, states)
    broad = strong(rows, states)
    congruence = C.immediate_congruence(rows, states)
    require(congruence == 194, 'candidate has an immediate-action quotient below194')

    frontier = sorted((ROOT/'comparison'/'frontier194').glob('*.tm'))
    diagnostics = sorted((ROOT/'comparison'/'nonspanning194').glob('*.tm'))
    require(len(frontier) == 548, 'incomplete or changed spanning comparison corpus')
    require(len(diagnostics) == 2, 'incomplete or changed diagnostic comparison corpus')
    strict_matches, broad_matches = [], []
    broad_forms, strict_forms = set(), set()
    congruences = collections.Counter()
    fingerprints = []
    for path in frontier:
        payload = path.read_bytes()
        rr, ss, _ = C.parse(payload)
        require(len(ss) == 194, 'non194 table in frontier: '+path.name)
        cc = C.canonical(rr, ss)
        require(cc is not None, 'nonspanning table in frontier: '+path.name)
        require(digest(cc) == path.stem, 'frontier canonical identity mismatch: '+path.name)
        bb = strong(rr, ss)
        # Compare actual canonical tuples; SHA256 is only an output identifier.
        if cc == strict:
            strict_matches.append(path.name)
        if bb == broad:
            broad_matches.append(path.name)
        strict_forms.add(cc)
        broad_forms.add(bb)
        congruences[C.immediate_congruence(rr, ss)] += 1
        fingerprints.append([path.name, C.sha(payload)])
    require(len(strict_forms) == 548 and len(broad_forms) == 548,
            'duplicate or changed frontier classes')
    require(digest(fingerprints) == EXPECTED_FRONTIER_MANIFEST,
            'frontier file manifest differs from the pinned comparison corpus')

    diagnostic_checks = []
    for path in diagnostics:
        payload = path.read_bytes()
        require(C.sha(payload) == path.stem, 'diagnostic byte identity mismatch: '+path.name)
        rr, ss, _ = C.parse(payload)
        require(len(ss) == 194 and C.canonical(rr, ss) is None,
                'diagnostic is not a nonspanning194-state table: '+path.name)
        # Having a spanning root is preserved by every symmetry above.
        diagnostic_checks.append({'file':path.name, 'sha256':C.sha(payload),
                                  'states':194, 'spanning_root':False,
                                  'excluded_by_spanning_invariant':True})

    parent_path = ROOT/'reference'/'AX11H'/'machine.tm'
    parent_rows, parent_states, _ = C.parse(parent_path.read_bytes())
    parent_form = strong(parent_rows, parent_states)
    require(parent_form in broad_forms, 'positive control: calibrated parent not recovered')
    renaming = {q:9000+31*q for q in parent_states}
    transformed = {}
    for (q, bit), (write, direction, nxt) in parent_rows.items():
        transformed[renaming[q], 1-bit] = (
            1-write, 'L' if direction == 'R' else 'R',
            renaming[nxt] if nxt in renaming else -99)
        if nxt not in renaming:
            transformed[renaming[q], 1-bit] = (0, 'R', -99)
    require(strong(transformed, sorted(renaming.values())) == parent_form,
            'positive control failed after combined structural symmetries')
    require(not strict_matches and not broad_matches, 'candidate is already in the pinned corpus')

    result = {
        'ok':True,
        'repository_commit':'7c0bb454cf73c29ca1c385f9fec856ddd236a7cb',
        'candidate':'machine/machine.tm',
        'candidate_sha256':C.sha(data),
        'working_states':194, 'rows':388, 'start':0, 'halt':194,
        'graph_reachable_from_start':reachable,
        'rooted_action_class':digest(rooted),
        'strict_graph_class':digest(strict), 'strong_graph_class':digest(broad),
        'strict_matches':strict_matches, 'strong_matches':broad_matches,
        'spanning194_classes_compared':len(frontier),
        'nonspanning194_diagnostics':diagnostic_checks,
        'distinct_strict_classes':len(strict_forms),
        'distinct_strong_classes':len(broad_forms),
        'candidate_immediate_action_congruence':congruence,
        'corpus_immediate_action_congruence_counts':dict(sorted(congruences.items())),
        'parent_positive_control':True,
        'combined_symmetry_positive_control':True,
        'frontier_manifest_sha256':digest(fingerprints),
        'pinned_frontier_manifest_verified':True,
        'comparison':'Exact canonical tuples over every spanning root, arbitrary control renaming, reflection, global symbol exchange, and erased halt-entry write/move.',
        'recognition_boundary':'The packaged pinned literal-table corpus. Arbitrary unexecuted generators, prose encodings, and direct tracked JSON outside the documented census are not claimed to have been exhaustively evaluated.',
        'claim_scope':'Structural novelty and finite table facts; this checker does not establish the inherited arithmetic consistency calibration.'
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
