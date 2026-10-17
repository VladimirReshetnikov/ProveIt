#!/usr/bin/env python3
"""Mixed-row folds across protected unary-register engine states.

The literal sample screen admits an arbitrary valid spare suffix. No passing
screen is claimed as an unbounded box theorem. The second stage assumes the
proposed relocated box interfaces, hence is explicitly conditional.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1] / 'source'
BASE = ROOT / 'Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0, str(BASE))
import candidate252_independent_audit as baseline
import breakthrough_register_permutation as affine
import permutation252_spare_fold_search as box


def make_table(table, dead, keep, bit):
    candidate = {k: (w,d,keep if t == dead else t)
                 for k,(w,d,t) in table.items() if k[0] != dead}
    w,d,t = table[dead,bit]
    candidate[keep,bit] = (w,d,keep if t == dead else t)
    assert len(candidate) == 502
    return candidate


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seconds', type=float, default=300)
    ap.add_argument('--fuel', type=int, default=2000)
    args = ap.parse_args()
    raw = (BASE/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes()
    assert hashlib.sha256(raw).hexdigest() == baseline.EXPECTED_SHA
    table = baseline.read_table(raw)
    cases = list(box.samples())
    usage, costs = [], []
    for i,case in enumerate(cases):
        ok,reason,used,ticks = box.run(table, case, args.fuel)
        assert ok, ('baseline',i,reason)
        usage.append(used)
        costs.append(ticks)
    states = sorted({q for q,_ in table})
    protected = baseline.BOX_STATES | {table[k][2] for k in baseline.BOX_PAIRS}
    # Dispatch stays literal. Pairs having one protected member orient that
    # member as dead. If both do, one orientation suffices up to label renaming.
    protected -= {96}
    recipes = []
    for dead in sorted(protected):
        for keep in states:
            if keep in (dead,96):
                continue
            if keep in protected and dead > keep:
                continue
            for bit in (0,1):
                if table[dead,bit] != table[keep,bit]:
                    recipes.append((dead,keep,bit))
    result = dict(scope=__doc__, source_sha256=baseline.EXPECTED_SHA,
                  baseline_samples=len(cases), fuel=args.fuel,
                  planned=len(recipes), tested=0, checks=0,
                  failures=[], literal_survivors=[])
    began = time.monotonic()
    print('BASELINE',len(cases),'PASS; recipes',len(recipes),flush=True)
    # Fresh, weakest-first ordering greatly reduces repeated full box scans.
    preferred = sorted(range(len(cases)), key=costs.__getitem__)
    for dead,keep,bit in recipes:
        if time.monotonic()-began > args.seconds:
            break
        candidate = make_table(table,dead,keep,bit)
        touched = {(dead,0),(dead,1),(keep,bit)}
        affected = [i for i in preferred if usage[i] & touched]
        affected_set = set(affected)
        order = affected + [i for i in preferred if i not in affected_set]
        for i in order:
            ok,reason,_,ticks = box.run(candidate,cases[i],args.fuel,dead,keep)
            result['checks'] += 1
            if not ok:
                result['failures'].append([dead,keep,bit,i,reason,ticks])
                break
        else:
            result['literal_survivors'].append([dead,keep,bit])
            if len(result['literal_survivors']) <= 8:
                print('LITERAL SURVIVOR',dead,keep,bit,flush=True)
        result['tested'] += 1
        if result['tested'] % 2000 == 0:
            print('PROGRESS',result['tested'],'/',len(recipes),'seconds',round(time.monotonic()-began,2),flush=True)
    result['status'] = 'complete' if result['tested']==len(recipes) else 'time_bound'
    result['sample_seconds'] = time.monotonic()-began
    result['failure_reasons'] = dict(Counter(x[4] for x in result['failures']))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    scratch=Path(tempfile.mkdtemp(prefix='zfc-box-mixed-affine-'))
    affine.prepare(ROOT,scratch)
    original_oracle=affine.strict.oracle
    assert affine.certify({(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in table.items()},baseline.PERM)['passed']
    result['conditional_affine'] = []
    for dead,keep,bit in result['literal_survivors']:
        def relocated(q,branch,state):
            candidates = [q]
            if q==str(keep):
                candidates.append(str(dead))
            answers = []
            for candidate in candidates:
                answer=original_oracle(candidate,branch,state)
                if answer is not None:
                    exit_state,effect=answer
                    answers.append((str(keep) if exit_state==str(dead) else exit_state,effect))
            if not answers:
                return None
            assert all(a==answers[0] for a in answers), ('incompatible proposed box APIs',q,state,answers)
            return answers[0]
        affine.strict.oracle=relocated
        candidate=make_table(table,dead,keep,bit)
        check=affine.certify({(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in candidate.items()},baseline.PERM)
        item=dict(dead=dead,keep=keep,bit=bit,check=check)
        result['conditional_affine'].append(item)
        if check['passed']:
            print('AFFINE SURVIVOR',dead,keep,bit,flush=True)
        if check['passed']:
            out=args.output.parent/f'box-mixed-{dead}-{keep}-{bit}.tm'
            out.write_text(f'#! start {keep if dead==64 else 64}\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(candidate.items())))
            item['table']=str(out)
    affine.strict.oracle=original_oracle
    result['total_seconds']=time.monotonic()-began
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('failures','scope','literal_survivors','conditional_affine')},indent=2),flush=True)
    print('Literal survivors:',len(result['literal_survivors']),'conditional affine survivors:',sum(x['check']['passed'] for x in result['conditional_affine']),flush=True)


if __name__=='__main__':main()
