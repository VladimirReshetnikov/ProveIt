#!/usr/bin/env python3
"""Prepare the literal Prog254 guard cases for independent C++ diagnostics.

The attributed source27 checker supplies baseline trace support only. This
preparation checks all 8,391 cases and the entire frozen 82,552-step bootstrap.
Nothing here proves a changed table, or runs a modified table from blank.
"""
import argparse, hashlib, importlib.util, json, re, sys
from collections import defaultdict
from pathlib import Path
from types import SimpleNamespace

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    base=a.repo/'Computability/BusyBeaver/Research/ZFC'
    audit=load('upstream_audit',base/'candidate252_independent_audit.py')
    raw=(base/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==audit.EXPECTED_SHA
    numeric=audit.read_table(raw)
    rows={(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in numeric.items()}
    source=a.repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    sys.modules['cost_search']=SimpleNamespace();strict=load('strict_for_actions',source)
    prog=a.repo/'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
    text=prog.read_text().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',text);assert len(nodes)==6459
    cases=[]
    def visit(q,p):
        for bit,e in enumerate(nodes[q]):
            path=p+str(bit);op,*arg=e.split();r=int(arg[0])if arg else None
            if op=='CN':visit(r,path);continue
            for zero in ((True,False)if op=='CD'else(None,)):
                physical=audit.NEWPHYS[r]if op in('CI','CD')else r
                branch=(physical,zero)if op=='CD'else None
                nxt=audit.successor(path,op,r,zero)
                effect=('inc',physical)if op=='CI'else('dec',physical)if op=='CD'and not zero else None
                right=([('b',int(c))for c in nxt]if nxt is not None else[])
                right += [('r',0,1,(41 if nxt is None else 40)-len(nxt or'')),('b',1),('box',('plain',effect))]
                cases.append((path,op,r,zero,branch,nxt,effect,strict.canon([('b',1)],right)))
    visit(0,'');assert len(cases)==8391
    class Tracking(dict):
        def __init__(self,r):super().__init__(r);self.used=set()
        def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)
    usage=defaultdict(set);costs={};lines=[]
    for i,(p,op,r,z,branch,nxt,effect,target)in enumerate(cases):
        traced=Tracking(rows);rules,literal=strict.run(traced,p,branch,target,halt=op=='CH',fuel=1000)
        assert literal>0;costs[i]=sum(rules.values())
        for q,b in traced.used:usage[int(q),b].add(i)
        breg,bzero=branch if branch is not None else(-1,-1)
        ekind=0 if effect is None else 2 if effect[0]=='inc'else 3
        ereg=-1 if effect is None else effect[1]
        lines.append(f'{p} {breg} {int(bzero)} {int(op=="CH")} {nxt if nxt else "_"} {41 if nxt is None else 40} {ekind} {ereg} {costs[i]}')
    q,h,one,_,_=audit.run_prefix(numeric,82552)
    spare=[0]*65;spare[8]=1
    assert(q,h,one)==(96,2,audit.paint('',40,[0]*9,spare,2))
    protected=audit.BOX_PAIRS;pt={numeric[k][2]for k in protected}
    states=sorted({q for q,b in numeric})
    eligible=[q for q in states if q not in {64,96}and q not in pt and all((q,b)not in protected for b in(0,1))]
    incoming={q:sorted(k for k,(_,_,t)in numeric.items()if t==q and k[0]!=q)for q in eligible}
    family=[q for q in eligible if len(incoming[q])==2]
    assert len(family)==46
    records=[]
    for q in family:
        inc=incoming[q]
        assert all(k[0]!=96 for k in inc)
        affected=sorted(usage[inc[0]]|usage[inc[1]],key=lambda i:(costs[i],i))
        assert affected
        records.append({'deleted':q,'incoming':inc,'affected':affected})
    records.sort(key=lambda x:(len(x['affected']),x['deleted']))
    a.out.mkdir(parents=True,exist_ok=True)
    (a.out/'cases.tsv').write_text('\n'.join(lines)+'\n')
    (a.out/'baseline.tm').write_bytes(raw)
    (a.out/'family.tsv').write_text('\n'.join(' '.join(map(str,[x['deleted'],*(v for row in x['incoming']for v in row),len(x['affected']),*x['affected']]))for x in records)+'\n')
    metadata={'baseline_cases':len(cases),'baseline_boot_steps':82552,'family_states':46,
        'actions_per_row':1008,'joint_recipes':46*1008**2,'ordering':[(x['deleted'],len(x['affected']))for x in records],
        'pinned_commit':'43026ff42f0939f09b9e95495248cfadcad38e38',
        'sources':{'table':audit.EXPECTED_SHA,'strict':hashlib.sha256(source.read_bytes()).hexdigest(),'Prog254':hashlib.sha256(prog.read_bytes()).hexdigest()},
        'scope':'Finite conditional diagnostic; no changed-table correctness or lower-bound claim.'}
    (a.out/'preparation.json').write_text(json.dumps(metadata,indent=2)+'\n');print(json.dumps(metadata))

if __name__=='__main__':main()
