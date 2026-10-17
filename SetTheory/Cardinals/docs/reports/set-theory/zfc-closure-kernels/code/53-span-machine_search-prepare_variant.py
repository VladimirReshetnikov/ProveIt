#!/usr/bin/env python3
"""Validate and prepare the All/Eq-tag-swap runtime for a fold screen."""
import argparse,hashlib,importlib.util,json,sys
from collections import defaultdict
from pathlib import Path
from types import SimpleNamespace
def load(name,path):
    s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def freeze(x):return tuple(map(freeze,x))if isinstance(x,list)else x
def main():
    p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--variant',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    a.out.mkdir(parents=True,exist_ok=True);base=a.repo/'Computability/BusyBeaver/Research/ZFC'
    audit=load('variant_audit',base/'candidate252_independent_audit.py')
    raw=(a.variant/'swap_tags_runtime_old.tm').read_bytes();casesraw=(a.variant/'swap_tags_guard_cases.json').read_bytes()
    (a.out/'baseline.tm').write_bytes(raw);(a.out/'source_cases.json').write_bytes(casesraw)
    numeric=audit.read_table(raw);baseline=audit.read_table((base/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes())
    assert all(numeric[k]==baseline[k]for k in audit.BOX_PAIRS)
    rows={(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in numeric.items()};states=sorted({q for q,b in numeric})
    assert len(states)==254 and all(t==254 or t in states for w,d,t in numeric.values())
    cases=json.loads(casesraw);assert len(cases)==8408
    sys.modules['cost_search']=SimpleNamespace()
    strict=load('variant_strict',a.repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py')
    class Tracking(dict):
        def __init__(self,r):super().__init__(r);self.used=set()
        def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)
    usage=defaultdict(set);costs={};lines=[]
    for i,c in enumerate(cases):
        assert c['index']==i
        pc=c['path'];branch=freeze(c['branch']);nxt=c['successor'];effect=freeze(c['effect']);target=freeze(c['target'])
        right=([('b',int(b))for b in nxt]if nxt is not None else[])+[('r',0,1,(41 if nxt is None else 40)-len(nxt or'')),('b',1),('box',('plain',effect))]
        assert strict.canon([('b',1)],right)==target
        tr=Tracking(rows);rules,literal=strict.run(tr,pc,branch,target,halt=c['halt'],fuel=1000);assert literal>0
        costs[i]=sum(rules.values())
        for q,b in tr.used:usage[int(q)].add(i)
        reg,z=branch if branch is not None else(-1,-1);ek=0 if effect is None else 2 if effect[0]=='inc'else 3;er=-1 if effect is None else effect[1]
        lines.append(f'{pc} {reg} {int(z)} {int(c["halt"])} {nxt if nxt else "_"} {41 if nxt is None else 40} {ek} {er} {costs[i]}')
    (a.out/'cases.tsv').write_text('\n'.join(lines)+'\n')
    pt={numeric[k][2]for k in audit.BOX_PAIRS}
    eligible=[q for q in states if q!=96 and q not in pt and all((q,b)not in audit.BOX_PAIRS for b in(0,1))]
    changed={76,183,190,210,215,217,232,234,239,240,241,246,255,256,257}
    eligible.sort(key=lambda q:(q<255,q not in changed,len(usage[q]),q))
    (a.out/'folds.tsv').write_text('\n'.join(' '.join(map(str,[q,len(usage[q]),*sorted(usage[q],key=lambda i:(costs[i],i))]))for q in eligible)+'\n')
    r={'baseline_states':len(states),'cases':len(cases),'eligible_deletions':eligible,'recipes':len(eligible)*(len(states)-1),
       'table_sha256':hashlib.sha256(raw).hexdigest(),'source_cases_sha256':hashlib.sha256(casesraw).hexdigest(),'protected_rows_unchanged':55,
       'scope':'Conditional finite affine fold screen of changed-codec runtime; blank initialization and ZFC calibration separate.'}
    (a.out/'preparation.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
if __name__=='__main__':main()
