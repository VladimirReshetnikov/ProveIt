#!/usr/bin/env python3
"""Replay all 8390 source cases with the inherited expanded symbolic checker.

The actual 242-state table is installed before re-proving the finite-block and
arbitrary-list induction templates. No Lean or Rocq compiler is invoked.
"""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import argparse, json, sys, time

TABLE_SHA = '6b700aa713418cfe347a6ff2d0a92de7c31810d1cf69814b4684c7fb463876a0'
SOURCE_SHA = '3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4'

def main():
    if not __debug__: raise RuntimeError('Python assertions must remain enabled.')
    ap = argparse.ArgumentParser()
    ap.add_argument('--reference', type=Path, required=True)
    ap.add_argument('--candidate', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    reference, candidate = a.reference.resolve(), a.candidate.resolve()
    before = {str(p.relative_to(reference)): sha256(p.read_bytes()).hexdigest()
              for p in sorted(reference.rglob('*')) if p.is_file() and '__pycache__' not in p.parts}
    tp, sp = candidate / 'zfc_return242_old.tm', candidate / 'sites_logical.json'
    assert sha256(tp.read_bytes()).hexdigest() == TABLE_SHA
    assert sha256(sp.read_bytes()).hexdigest() == SOURCE_SHA
    sys.path.insert(0, str(reference / 'code'))
    import full_symbolic_parametric as F
    T, start = F.rebuild.read_table(tp)
    assert start == 95 and len(T) == 484 and len({q for q,b in T}) == 242
    assert 15 not in {q for q,b in T} and all(r != 15 for w,d,r in T.values())
    assert F.PADDING == 64
    F.m.TABLE = T
    F.m.prove_blocks()
    F.m.prove_word_identity()
    sites = json.loads(sp.read_text())
    assert len(sites) == 6459
    counts, rules, used, records = Counter(), Counter(), set(), []
    began = time.monotonic()
    for i, (pc, op, r) in enumerate(sites):
        for zero in ((True, False) if op == 'CD' else (None,)):
            result = F.case(pc, op, r, zero, [[0,9]] * 9)
            for row in result['trace']:
                if 'state' in row: used.add((row['state'], row['read']))
                rules[row['rule']] += 1
            counts['cases'] += 1
            counts['symbolic_rules'] += result['rules']
            records.append(dict(index=i, pc=pc, op=op, r=r, zero=zero,
                                **{k:v for k,v in result.items() if k!='trace'}))
        if i % 500 == 0:
            print('expanded source sites', i, 'cases', counts['cases'], flush=True)
    assert counts['cases'] == 8390
    assert used == set(T), ('Uncovered or unexpected row', set(T)-used, used-set(T))
    after = {str(p.relative_to(reference)): sha256(p.read_bytes()).hexdigest()
             for p in sorted(reference.rglob('*')) if p.is_file() and '__pycache__' not in p.parts}
    assert before == after
    assert sha256(tp.read_bytes()).hexdigest() == TABLE_SHA
    assert sha256(sp.read_bytes()).hexdigest() == SOURCE_SHA
    out = dict(status='PASS_RETURN242_UNIVERSAL_EXPANDED_RUNTIME', complete=True,
               working_states=242, source_leaves=len(sites), expected_cases=8390,
               counts=dict(counts), rules=dict(rules), literal_rows_covered=len(used),
               unused_rows=[], rows=sorted(used), frame_padding=64,
               arbitrary_primary_registers=True, arbitrary_nonnegative_gap=True,
               arbitrary_nonempty_finite_spare_suffix=True, positive_progress_checked=True,
               table_sha256=TABLE_SHA, source_sha256=SOURCE_SHA,
               reference_inputs=before, all_input_postchecks=True,
               seconds=time.monotonic()-began, cases=records,
               scope='Ordinary symbolic induction-certificate replay on actual242 table; no proof-assistant consistency endpoint.')
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('cases','rows','reference_inputs')}, indent=2), flush=True)

if __name__ == '__main__': main()
