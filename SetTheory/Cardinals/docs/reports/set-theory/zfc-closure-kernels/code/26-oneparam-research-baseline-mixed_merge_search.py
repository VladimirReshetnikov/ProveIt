#!/usr/bin/env python3
"""Bounded mixed-row state amalgamations of the actual public 253 machine.

For each unordered pair of non-interface states p<q, delete p, redirect p
to q, and choose exactly one row of p and the other row of q for q. The two
unmixed choices were covered by earlier direct-fold searches and are omitted.
All 55 protected box rows must be literally identical after rewriting.

The unchanged attributed affine design executor is experimental evidence.
Success would require every runtime case, exact blank initialization and a
separate soundness/kernel argument. Failures are not machine lower bounds.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import importlib.util
import itertools
import json
import sys
import time

if not __debug__:
    raise SystemExit('Run without -O; assertions are input-identity checks.')
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'helpers'))
import context_search as cs
spec = importlib.util.spec_from_file_location('generate_candidate', ROOT / 'busy-beaver/ZF/m253/tools/generate_candidate.py')
gc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gc)

BOX_STATES = {0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}
PROTECTED = {(str(q), b) for q in BOX_STATES for b in (0,1)} - {('3',0)}
assert len(PROTECTED) == 55


class Tracked(dict):
    def __init__(self, rows):
        super().__init__(rows)
        self.used = set()
    def __getitem__(self, key):
        self.used.add(key)
        return super().__getitem__(key)


def run_case(ns, cases, current, i, fuel):
    _, path, op, _, branch, expected = cases[i]
    ns['T'] = current
    try:
        result = ns['run']('96', [('b', 1)], ns['tape_R'](path, 0, ()), branch, expected, fuel=fuel)
        if result[0] == ('halt' if op == 'CH' else 'ok'):
            return {'pass': True, 'steps': result[1]}
        return {'pass': False, 'reason': 'unexpected_status', 'status': result[0]}
    except (ns['Fail'], KeyError) as exc:
        return {'pass': False, 'reason': type(exc).__name__, 'detail': str(exc)}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--fuel', type=int, default=1000)
    ap.add_argument('--output', type=Path, default=ROOT/'mixed_merge_results.json')
    args = ap.parse_args()
    base = ROOT/'busy-beaver/ZF/m254/machine/zfc_254.tm'
    public = ROOT/'busy-beaver/ZF/m253/machine/zfc_253.tm'
    assert public.read_bytes() == gc.generate_candidate(base)
    table = {(str(q), b): (w, d, str(n)) for (q,b), (w,d,n) in gc.patched_rows(base).items()}
    ns = cs.executor(table, ROOT/'busy-beaver/ZF/m254/tools/tm/symexec.py')
    sites = cs.program_sites(ROOT/'busy-beaver/ZF/m254/coq/tm/Prog254.v')
    cases = cs.cases(ns, sites)
    assert len(cases) == 8391
    use = collections.defaultdict(set)
    cost = []
    begin = time.monotonic()
    for i in range(len(cases)):
        traced = Tracked(table)
        result = run_case(ns, cases, traced, i, args.fuel)
        assert result['pass'], (i, result)
        cost.append(result['steps'])
        for row in traced.used:
            use[row].add(i)
    print('BASELINE 8391 PASS; 55 protected rows', flush=True)
    state_order = sorted({q for q,b in table}, key=int)
    # Deleting or overwriting a protected row is inadmissible. The dispatcher
    # is fixed because the imported site interface explicitly stops there.
    eligible = [q for q in state_order if int(q) not in BOX_STATES | {96}]
    report = {
        'status':'running', 'public_pin':'0d544f2a2e3c18f12278441a74b7879f31cbe856',
        'public_table_sha256': hashlib.sha256(public.read_bytes()).hexdigest(),
        'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'attribution':'Mira-Cult 254; mira-emmy 253; Jeff affine executor; Wade framework; ProveIt source04 parser/case scaffolding',
        'scope':'two mixed row choices per unordered pair, same dispatch contract at arbitrary affine gap>=40; diagnostic, not kernel proof',
        'baseline_cases':len(cases), 'fuel_per_case':args.fuel,
        'eligible_old_labels':list(map(int,eligible)),
        'protected_rows':[[int(q),b] for q,b in sorted(PROTECTED,key=lambda x:(int(x[0]),x[1]))],
        'candidates':[], 'survivors':[], 'kernel_proof':False,
        'global_minimality_claimed':False
    }
    outcomes=collections.Counter()
    for p,q in itertools.combinations(eligible,2):
        for from_p in (0,1):
            # p and q are merged; the row on from_p comes from p. The other
            # row is q's. All outgoing p targets are also rewritten to q.
            candidate = {k:(w,d,q if n==p else n) for k,(w,d,n) in table.items() if k[0]!=p}
            w,d,n=table[p,from_p]
            candidate[q,from_p]=(w,d,q if n==p else n)
            record={'deleted_old':int(p),'retained_old':int(q),'read_from_deleted':from_p,
                    'start_old':int(q if p=='5' else '5')}
            bad=[[int(a),b] for a,b in PROTECTED if candidate.get((a,b))!=table[a,b]]
            if bad:
                record.update(outcome='protected_row_changed',rows=bad)
            else:
                assert len(candidate)==504
                allowed_targets=set(state_order)-{p}|{'254'}
                assert all(n in allowed_targets for w,d,n in candidate.values())
                changed=[k for k in table if candidate.get(k)!=table[k]]
                affected=set().union(*(use[k] for k in changed))
                indices=sorted(affected,key=lambda i:(cost[i],i))
                record['affected_cases']=len(indices)
                record['changed_rows']=[[int(a),b] for a,b in changed]
                record['checked_cases']=0
                for i in indices:
                    result=run_case(ns,cases,candidate,i,args.fuel)
                    record['checked_cases']+=1
                    if not result['pass']:
                        record.update(outcome='affine_rejected',first_failure={'case':i,**result})
                        break
                else:
                    for i in range(len(cases)):
                        result=run_case(ns,cases,candidate,i,args.fuel)
                        record['checked_cases']+=1
                        if not result['pass']:
                            record.update(outcome='full_recheck_rejected',first_failure={'case':i,**result})
                            break
                    else:
                        record['outcome']='all8391_passed'
                        report['survivors'].append(record.copy())
                        out=ROOT/f'mixed_survivor_{p}_{q}_{from_p}.tm'
                        out.write_text(f'#! start {record["start_old"]}\n'+''.join(
                            f'{a} {b} {w} {d} {n}\n' for (a,b),(w,d,n) in sorted(candidate.items(),key=lambda x:(int(x[0][0]),x[0][1]))))
                        print('SURVIVOR',record,flush=True)
            report['candidates'].append(record)
            outcomes[record['outcome']]+=1
        if len(report['candidates'])%10000==0:
            print('PROGRESS',len(report['candidates']),dict(outcomes),'seconds',round(time.monotonic()-begin,2),flush=True)
    report.update(status='completed',outcomes=dict(outcomes),elapsed_seconds=time.monotonic()-begin)
    report['rejection_reasons']=dict(collections.Counter(c.get('first_failure',{}).get('detail','') for c in report['candidates'] if c['outcome'].endswith('rejected')))
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('status','outcomes','survivors','elapsed_seconds','rejection_reasons')},indent=2),flush=True)
    print('Evidence:',args.output,flush=True)


if __name__=='__main__':
    main()
