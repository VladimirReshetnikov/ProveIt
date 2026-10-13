"""Deterministic exhaustive audits; run with PYTHONPATH=src:tests."""
import itertools as it
import json
import time
from pathlib import Path
from private_cocore import *
from private_cocore.atlas import merge, multiply
from reference import dense_replay, private_rows

start = time.perf_counter()
counts = dict(schedule_validity_checks=0, accepted_zero_fill=0,
              passive_differential_cases=0, source_unit_matching_checks=0,
              matching_order_replays=0, signature_addition_cases=0,
              signature_scalar_cases=0)
for entries in it.product(range(3), repeat=6):
    real = [{h: entries[3*r+h] for h in range(3) if entries[3*r+h]} for r in range(2)]
    for columns in it.permutations(range(3), 2):
        for order in ((0, 1), (1, 0)):
            schedule = [(r, columns[r]) for r in order]
            try:
                p = compile_program(real, 3, schedule); actual = True
            except ValueError:
                actual = False
            try:
                dense_replay(real, 3, [], schedule, zero_fill_only=True); expected = True
            except ValueError:
                expected = False
            assert actual == expected, (real, schedule)
            counts['schedule_validity_checks'] += 1
            if not actual:
                continue
            counts['accepted_zero_fill'] += 1
            for bits in it.product(range(2), repeat=6):
                passive = [{h: bits[3*r+h] for h in range(3) if bits[3*r+h]} for r in range(2)]
                exact, live = dense_replay(real, 3, passive, schedule)
                cert = produce_certificate(real, 3, passive, schedule)
                assert tuple(cert['least_private']) == private_rows(exact, live)
                assert verify_certificate(real, 3, passive, cert)
                counts['passive_differential_cases'] += 1
        # A fixed SOURCE-unit matching: compare normalization against every order.
        if any(real[r].get(columns[r]) != 1 for r in range(2)):
            continue
        matching = [(r, columns[r]) for r in range(2)]
        counts['source_unit_matching_checks'] += 1
        try:
            normal = normalize_matching(real, 3, matching); accepted = True
        except ValueError:
            accepted = False
        for order in ((0, 1), (1, 0)):
            schedule = [(r, columns[r]) for r in order]
            try:
                dense_replay(real, 3, [], schedule); complete = True
            except ValueError:
                complete = False
            assert complete == accepted
            if accepted:
                # each single basis seed independently checks the whole transfer map
                passive = [{h: 1} for h in range(3)]
                result, live = dense_replay(real, 3, passive, schedule)
                norm_result, norm_live = dense_replay(real, 3, passive, normal)
                assert result == norm_result and live == norm_live
                counts['matching_order_replays'] += 1

vectors = list(it.product(range(3), repeat=4))
def project(v, limit):
    out = tuple((i, min(2, x)) for i, x in enumerate(v) if x)
    return out if len(out) <= limit else None
for k in range(4):
    for a in vectors:
        for b in vectors:
            assert merge(project(a,k+1), project(b,k+1), k+1) == project([x+y for x,y in zip(a,b)], k+1)
            counts['signature_addition_cases'] += 1
        for w in range(4):
            assert multiply(project(a,k+1),w) == project([w*x for x in a],k+1)
            counts['signature_scalar_cases'] += 1
counts['seconds'] = time.perf_counter() - start
counts['status'] = 'PASS'
Path('data/exhaustive-audit.json').write_text(json.dumps(counts, indent=2)+'\n')
print(json.dumps(counts, indent=2))
