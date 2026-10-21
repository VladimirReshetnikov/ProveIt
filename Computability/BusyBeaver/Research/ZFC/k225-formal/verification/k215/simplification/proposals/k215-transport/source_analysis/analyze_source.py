#!/usr/bin/env python3
"""Reproduce structural measurements of the pinned K215 source certificate.

This is an ordinary finite computation, not a Lean/Rocq proof or a new
machine-size bound. The certificate generator is the unmodified repository
reference; caching only memoizes pure functions.
"""
from collections import Counter
from functools import lru_cache
from pathlib import Path
import hashlib
import json
import gen_cert_reference as cert

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def analyze():
    cert.Tree.tsite = lru_cache(maxsize=None)(cert.Tree.tsite)
    cert.seg = lru_cache(maxsize=None)(cert.seg)
    left = cert.Tree(cert.load(HERE / 'inputs/sites215.json'))
    right = cert.Tree(cert.load(HERE / 'inputs/dagperm_sites.json'))
    entries = cert.generate(left, right)
    labels = []
    for a, b, offset, yes, no in entries:
        assert offset == 0
        (op, arg), q = left.tsite(a)
        (op2, arg2), r = right.tsite(b)
        assert (op, arg) == (op2, arg2)
        if op == 'EHalt':
            labels.append(('HALT',))
            continue
        plus = cert.seg(left, cert.inc_path(q))[0]
        zero = cert.seg(left, cert.brk(1, q))[0]
        plus2 = cert.seg(right, cert.inc_path(r))[0]
        zero2 = cert.seg(right, cert.brk(1, r))[0]
        assert Counter(plus) == Counter(plus2)
        assert Counter(zero) == Counter(zero2)
        labels.append((arg, tuple(sorted(Counter(plus).items())),
                       tuple(sorted(Counter(zero).items()))))

    # Partition refinement on the deterministic labelled checkpoint graph.
    # The HALT case deliberately ignores the certificate's dummy successors.
    unique = {x: i for i, x in enumerate(sorted(set(labels), key=str))}
    classes = [unique[x] for x in labels]
    class_counts = [len(unique)]
    while True:
        signatures = [label if label == ('HALT',) else
                      (label, classes[e[3]], classes[e[4]])
                      for label, e in zip(labels, entries)]
        unique = {x: i for i, x in enumerate(sorted(set(signatures), key=str))}
        new = [unique[x] for x in signatures]
        class_counts.append(len(unique))
        # Each new partition refines the old one. Equal cardinality is enough
        # only after checking that refinement explicitly.
        parents = {}
        for old, fresh in zip(classes, new):
            assert parents.setdefault(fresh, old) == old
        if len(set(new)) == len(set(classes)):
            classes = new
            break
        classes = new

    # Independently check that the returned quotient is a graph congruence.
    representatives = {}
    for i, cls in enumerate(classes):
        sig = labels[i] if labels[i] == ('HALT',) else (
            labels[i], classes[entries[i][3]], classes[entries[i][4]])
        assert representatives.setdefault(cls, sig) == sig
    report = {
        'repository_commit': 'b6c7087477e51c017003bd729e712c8969733223',
        'status': 'FINITE_STRUCTURAL_AUDIT_PASS',
        'inputs': {p.name: sha(p) for p in [HERE/'gen_cert_reference.py',
                   HERE/'inputs/sites215.json', HERE/'inputs/dagperm_sites.json']},
        'paired_checkpoints': len(entries),
        'nonzero_offsets': sum(e[2] != 0 for e in entries),
        'local_effect_signatures': len(set(labels)),
        'stable_graph_classes': len(set(classes)),
        'partition_refinement_counts': class_counts,
        'maximum_checkpoint_path_lengths': [max(len(e[j]) for e in entries)
                                             for j in [0, 1]],
        'quotient_check': 'Every class preserves halt/test label, branch effects, and successor classes.',
        'scope': ('Potential source-certificate compression only. All literal-path bindings '
                  'still require proof. No kernel speedup, shorter TM, or new consistency '
                  'calibration is claimed.')
    }
    (HERE/'source_analysis.json').write_text(json.dumps(report, indent=2)+'\n')
    (HERE/'quotient_certificate.json').write_text(json.dumps({
        'classes': classes, 'representatives': representatives}, separators=(',', ':'))+'\n')
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ['partition_refinement_counts', 'inputs']}, indent=2))


if __name__ == '__main__':
    analyze()
