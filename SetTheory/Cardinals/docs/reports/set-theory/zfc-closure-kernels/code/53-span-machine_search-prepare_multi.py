#!/usr/bin/env python3
"""Prepare all eligible incoming-action families from the validated cases.

The 55 box-support rows and BOTH literal dispatch rows remain fixed. A
deleted state's self-loop rows disappear; only its external incoming rows
require choices. Each replacement target is retained, or is the halt label.
"""
import argparse, hashlib, importlib.util, json, sys
from collections import defaultdict
from pathlib import Path
from types import SimpleNamespace

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--data',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args();base=a.repo/'Computability/BusyBeaver/Research/ZFC'
    audit=load('multi_audit',base/'candidate252_independent_audit.py')
    raw=(a.data/'baseline.tm').read_bytes();assert hashlib.sha256(raw).hexdigest()==audit.EXPECTED_SHA
    numeric=audit.read_table(raw);rows={(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in numeric.items()}
    source=a.repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    sys.modules['cost_search']=SimpleNamespace();strict=load('multi_strict',source)
    class Tracking(dict):
        def __init__(self,r):super().__init__(r);self.used=set()
        def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)
    usage=defaultdict(set);costs={}
    lines=(a.data/'cases.tsv').read_text().splitlines();assert len(lines)==8391
    for i,line in enumerate(lines):
        pc,reg,zero,halt,nxt,gap,effect,ereg,cost=line.split()
        reg,zero,halt,gap,effect,ereg,cost=map(int,(reg,zero,halt,gap,effect,ereg,cost))
        nxt=''if nxt=='_'else nxt
        branch=None if reg<0 else(reg,bool(zero))
        effect=None if effect==0 else('inc'if effect==2 else'dec',ereg)
        right=[('b',int(c))for c in nxt]+[('r',0,1,gap-len(nxt)),('b',1),('box',('plain',effect))]
        traced=Tracking(rows);rules,literal=strict.run(traced,pc,branch,strict.canon([('b',1)],right),halt=bool(halt),fuel=1000)
        assert literal>0 and sum(rules.values())==cost
        costs[i]=cost
        for q,b in traced.used:usage[int(q),b].add(i)
    states=sorted({q for q,b in numeric});protected=audit.BOX_PAIRS;pt={numeric[k][2]for k in protected}
    eligible=[q for q in states if q not in {64,96}and q not in pt and all((q,b)not in protected for b in(0,1))]
    records=[];removed_for_dispatch=[]
    for q in eligible:
        incoming=sorted(k for k,(_,_,t)in numeric.items()if t==q and k[0]!=q)
        if any(k[0]==96 for k in incoming):removed_for_dispatch.append(q);continue
        assert incoming and all(k not in protected for k in incoming)
        assert all(k[0]==q or k in incoming for k,v in numeric.items()if v[2]==q)
        affected=sorted(set.union(*(usage[k]for k in incoming)),key=lambda i:(costs[i],i))
        assert affected
        records.append({'deleted':q,'degree':len(incoming),'incoming':incoming,'affected':affected,
                        'self_loop_rows':[k for k,v in numeric.items()if k[0]==q and v[2]==q]})
    records.sort(key=lambda x:(x['degree'],len(x['affected']),x['deleted']))
    a.out.mkdir(parents=True,exist_ok=True)
    for name in('baseline.tm','cases.tsv'):(a.out/name).write_bytes((a.data/name).read_bytes())
    (a.out/'family.tsv').write_text('\n'.join(' '.join(map(str,[x['degree'],x['deleted'],*(v for row in x['incoming']for v in row),len(x['affected']),*x['affected']]))for x in records)+'\n')
    metadata={'eligible_states':len(records),'removed_to_keep_dispatch_rows_fixed':removed_for_dispatch,
        'groups':[{k:v for k,v in x.items()if k!='affected'}|{'affected_count':len(x['affected'])}for x in records],
        'degree_counts':{d:sum(x['degree']==d for x in records)for d in sorted({x['degree']for x in records})},
        'actions_per_incoming':1008,'total_concrete_assignments':sum(1008**x['degree']for x in records),
        'baseline_cases':8391,'table_sha256':audit.EXPECTED_SHA,
        'cases_sha256':hashlib.sha256((a.data/'cases.tsv').read_bytes()).hexdigest(),
        'protected_rows':55,'fixed_dispatch_rows':[[96,0],[96,1]],'fixed_blank_start':64,
        'scope':'Conditional finite search; no machine equivalence or lower bound follows from a failed check.'}
    (a.out/'preparation.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps({k:v for k,v in metadata.items()if k!='groups'}))

if __name__=='__main__':main()
