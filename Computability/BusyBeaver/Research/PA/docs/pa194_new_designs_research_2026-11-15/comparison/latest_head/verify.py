#!/usr/bin/env python3
"""Offline identity, class and exhaustive explicit-bijection replay for the
eight post-snapshot 194-state classes. Uses only the Python standard library.

Symbol exchange is an extra structural screen, not a zero-blank semantic
equivalence. Halt-entry writes and moves are erased in the novelty screen.
This verifies structural novelty, not the correctness of imported machines.
"""
from pathlib import Path
import argparse, csv, hashlib, json, sys

HERE = Path(__file__).resolve().parent
CORE = HERE.parent
sys.path.insert(0, str(CORE))
import literal_inventory as lit
import machine_classes as mc
from novelty_check import match, spanning
from verify_corpus import congruence

def main():
    assert __debug__, 'Run without Python -O.'
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lcsf3', type=Path, default=CORE.parent/'construction/candidate/machine.tm')
    ap.add_argument('--mp', type=Path, default=CORE.parent/'mp_construction/candidate/machine.tm')
    ap.add_argument('--output', type=Path, default=HERE/'verification.json')
    a = ap.parse_args()
    old_frontier = json.loads((CORE/'census/frontier194.json').read_text())
    old_keys = {r['table_class'] for r in old_frontier}
    assert len(old_keys) == 520
    extras = json.loads((HERE/'extra_named_designs8.json').read_text())
    rejected = json.loads((HERE/'extra193.json').read_text())
    assert len(extras) == 8 and len(rejected) == 1
    extra_keys = {r['table_class'] for r in extras}
    assert len(extra_keys) == 8 and not (old_keys & extra_keys)
    named = list(csv.DictReader((CORE/'named_designs83.csv').open()))
    assert len(named) == 83
    assert not ({r['name'] for r in extras} & {r['name'] for r in named})
    assert len(json.loads((CORE/'packet_ledger97.json').read_text())) == 97
    assert len(json.loads((HERE/'archive_identities.json').read_text())) == 3
    verified, corpus = [], []
    for record in extras + rejected:
        b = (HERE/record['representative']).read_bytes()
        assert hashlib.sha256(b).hexdigest() == record['sha256']
        data = lit.parse_table(b)
        assert data is not None
        c = mc.classify(b)
        assert c['table'] == record['table_class']
        assert c['states'] == record['states']
        assert spanning(data) is not None
        n = congruence(*data)
        verified.append(dict(name=record['name'], table_class=c['table'],
                             states=c['states'], sha256=record['sha256'],
                             immediate_action_congruence_classes=n))
        if record in extras:
            assert n == 194
            corpus.append((record, data))
    candidates = [('PA194-LCSF3', a.lcsf3,
                   '2e5684567cd6e6e59fd99b5b093071533bcef6a01012dd2c6e41d52c645d2768'),
                  ('PA194-MP', a.mp,
                   'b634f75f4969a68513c5460a2e6bf8fd9bb0a72ab1f3dd03ec88b348ce2c6272')]
    results = []
    for label, path, expected_sha in candidates:
        b = path.read_bytes()
        digest = hashlib.sha256(b).hexdigest()
        assert digest == expected_sha
        data = lit.parse_table(b)
        assert data is not None and len(data[1]) == 194
        root = spanning(data)
        assert root is not None
        attempts, matches = 0, []
        for record, other in corpus:
            for reflection, complement in [(False, False), (True, False),
                                            (False, True), (True, True)]:
                for q in sorted(other[1]):
                    attempts += 1
                    bijection = match(data, root, other, q, reflection, complement)
                    if bijection is not None:
                        matches.append(dict(name=record['name'],
                            table_class=record['table_class'], candidate_root=root,
                            corpus_root=q, reflection=reflection,
                            symbol_exchange=complement, bijection=bijection))
        assert attempts == 8 * 194 * 4 == 6208
        assert not matches
        results.append(dict(name=label, sha256=digest, extra_classes=8,
            rooted_bijection_attempts=attempts, matches=matches,
            structurally_new_to_extra_classes=True))
    changes = json.loads((HERE/'PA_blob_changes.json').read_text())['changed_blobs']
    assert len(changes) == 98
    explicit = {'.tm', '.json', '.txt', '.csv', '.tsv', '.zip'}
    assert not [r for r in changes if Path(r['path']).suffix in explicit]
    result = dict(status='PASS', pin='99f17206a77a04d36a9bb7dd04ce2e5d0360cf7d',
        scope=__doc__, prior_deliveries=97, extra_deliveries=3, combined_deliveries=100,
        prior_named_designs=83, extra_named_designs=8, combined_named_designs=91,
        prior_spanning194_classes=520, extra_spanning194_classes=8,
        combined_spanning194_classes=528, PA_changed_blobs=98,
        PA_changed_explicit_table_inputs=0, representatives=verified,
        candidate_results=results)
    a.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
