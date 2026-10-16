#!/usr/bin/env python3
"""Finite candidate search on the exact M253 table under existing box contracts.

For each retained/deleted pair, each branch is independently selected from one
of the original states. Full-table target redirection follows. This strictly
extends direct state redirection, while preserving every protected box row.
All 8,391 affine cases and the complete blank bootstrap are checked for any
survivor. This is Python diagnostic evidence, not a kernel theorem.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from collections import Counter
import csv
import gzip
import hashlib
import itertools
import json
from pathlib import Path
import sys
import time
import context_search as c


def dump(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')


class Trace(dict):
    def __init__(self, table):
        super().__init__(table)
        self.used = set()
    def __getitem__(self, key):
        self.used.add(key)
        return super().__getitem__(key)


def bootstrap(table, start, steps=312975):
    ones=set(); q=start; h=0
    for i in range(steps):
        try: w,d,t=table[q,int(h in ones)]
        except KeyError: return None
        if w: ones.add(h)
        else: ones.discard(h)
        h += 1 if d=='R' else -1
        q=t
    return q,h,sorted(ones)


def diagnose(ns, case, fuel):
    _, path, op, _, branch, expect=case
    try:
        result=ns['run']('96',[('b',1)],ns['tape_R'](path,0,()),branch,expect,fuel=fuel)
    except ns['Fail'] as error:
        detail=str(error)
        kind='fuel_exhausted' if detail=='fuel' else 'symbolic_abstraction_limit'
        return False,kind,detail
    except KeyError as error:
        return False,'missing_transition',str(error)
    expected='halt' if op=='CH' else 'ok'
    if result[0]!=expected:
        return False,'unexpected_halt' if result[0]=='halt' else 'unexpected_normal_return',str(result)
    return True,'pass',''


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--fuel', type=int, default=1000)
    args=p.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    source=args.repo/'lib/jeff-busy-beaver-zfc254/ZF/m254'
    rows, _, _, _, sha=c.parse_table(source/'machine/zfc_254.tm')
    assert sha=='d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb'
    table={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in rows.items() if q!=8}
    table.update({('3',0):(0,'L','48'),('5',0):(1,'R','97'),
                  ('5',1):(1,'R','64'),('49',1):(0,'R','5')})
    box_states={0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,
                63,64,69,73,75,83,85,95,97,109,112,131}
    protected={(str(q),b) for q in box_states for b in (0,1)}-{('3',0)}
    assert len(protected)==55
    ns=c.executor(table,source/'tools/tm/symexec.py')
    allcases=c.cases(ns,c.program_sites(source/'coq/tm/Prog254.v'))
    usage=defaultdict(set)
    lengths={}
    for i,case in enumerate(allcases):
        tr=Trace(table); ns['T']=tr
        assert c.check(ns,case,args.fuel), ('baseline failed',i)
        for pair in tr.used: usage[pair].add(i)
        lengths[i]=len(tr.used)
    target=bootstrap(table,'5'); assert target and target[:2]==('96',-17)
    states=sorted({q for q,b in table},key=int)
    forbidden_dead={q for q,b in protected}|{table[p][2] for p in protected}|{'96'}
    deletes=[q for q in states if q not in forbidden_dead]
    report={'source_commit':'de047657e193ec605e930eaf149a44a38031820b',
            'upstream253_commit':'0d544f2a2e3c18f12278441a74b7879f31cbe856',
            'baseline_runtime_cases_passed':len(allcases),'fuel':args.fuel,
            'bootstrap_steps':312975,'bootstrap_ones':len(target[2]),
            'protected_pairs':len(protected),'forbidden_deleted_states':sorted(forbidden_dead,key=int),
            'eligible_deleted_states':deletes,'tested':0,'rejected_by_box_preservation':0,
            'affine_survivors':[],'bootstrap_survivors':[],
            'scope':'Finite symbol-wise fusion search, existing box contracts, no new kernel proof.'}
    dump(args.out/'pair_usage.json',{f'{q}/{b}':len(v) for (q,b),v in usage.items()})
    print('baseline cases',len(allcases),'eligible deletes',len(deletes),'bootstrap exact',len(target[2]),flush=True)
    begin=time.monotonic()
    seen=set()
    census=Counter();details=Counter()
    ledger_file=gzip.open(args.out/'rejection_ledger.csv.gz','wt',newline='')
    ledger=csv.writer(ledger_file)
    ledger.writerow(['deleted','retained','take_deleted_read0','take_deleted_read1','case_index','reason','detail'])
    for n,a in enumerate(deletes):
        for b in states:
            if b==a: continue
            for take_a in itertools.product((False,True),repeat=2):
                if not any(take_a): continue  # direct redirects already exhaustively searched upstream
                merged={bit:table[(a if take_a[bit] else b),bit] for bit in (0,1)}
                key=tuple(merged[bit] for bit in (0,1))
                if key==tuple(table[b,bit] for bit in (0,1)): continue
                def redirect(row):
                    w,d,t=row
                    return (w,d,b if t==a else t)
                candidate={k:redirect(row) for k,row in table.items() if k[0]!=a}
                candidate.update({(b,bit):redirect(merged[bit]) for bit in (0,1)})
                if any(candidate[p]!=table[p] for p in protected):
                    report['rejected_by_box_preservation']+=1;continue
                identifier=(a,b,tuple(candidate[b,bit] for bit in (0,1)))
                if identifier in seen:continue
                seen.add(identifier)
                report['tested']+=1
                affected=usage[a,0]|usage[a,1]
                for bit in (0,1):
                    if candidate[b,bit]!=table[b,bit]: affected=affected|usage[b,bit]
                ns['T']=candidate
                rejected=False
                for i in sorted(affected,key=lambda i:lengths[i]):
                    good,reason,detail=diagnose(ns,allcases[i],args.fuel)
                    if not good:
                        census[reason]+=1;details[detail]+=1
                        ledger.writerow([a,b,int(take_a[0]),int(take_a[1]),i,reason,detail])
                        rejected=True;break
                if rejected:continue
                if not all(c.check(ns,case,args.fuel) for case in allcases):continue
                item={'deleted':a,'retained':b,'take_deleted_rows':take_a,
                      'merged_rows':[candidate[b,bit] for bit in (0,1)]}
                report['affine_survivors'].append(item)
                boot=bootstrap(candidate,b if a=='5' else '5')
                item['exact_bootstrap_match']=boot==target
                print('AFFINE SURVIVOR',item,flush=True)
                if boot==target:
                    report['bootstrap_survivors'].append(item)
                    data='#! start '+(b if a=='5' else '5')+'\n'+''.join(f'{q} {bit} {w} {d} {t}\n' for (q,bit),(w,d,t) in sorted(candidate.items(),key=lambda kv:(int(kv[0][0]),kv[0][1])))
                    (args.out/f'candidate-{a}-to-{b}-{int(take_a[0])}{int(take_a[1])}.tm').write_text(data)
        if n%20==0:
            report['elapsed_seconds']=time.monotonic()-begin
            dump(args.out/'fusion_results.json',report)
            print('deleted sources',n+1,'/',len(deletes),'tested',report['tested'],'elapsed',round(report['elapsed_seconds'],2),flush=True)
    report['elapsed_seconds']=time.monotonic()-begin
    ledger_file.close()
    report['first_rejection_reason_census']=dict(census)
    report['first_rejection_detail_census']=dict(details)
    report['ledger_sha256']=hashlib.sha256((args.out/'rejection_ledger.csv.gz').read_bytes()).hexdigest()
    report['negative_scope']='No accepted candidate under this symbolic abstraction/fuel; abstraction failures and timeouts are not semantic counterexamples.'
    dump(args.out/'fusion_results.json',report)
    print(json.dumps({k:v for k,v in report.items() if k not in ('eligible_deleted_states','forbidden_deleted_states')},indent=2))

if __name__=='__main__':main()
