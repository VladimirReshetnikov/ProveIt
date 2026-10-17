#!/usr/bin/env python3
"""Two-row mixed merges with literal register-box tests and affine screening.

This search extends the pinned spare-suffix uniform-fold family to mixed rows.
Passing finite box tests does not prove an unbounded register-box contract.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import time
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'sources'))
import candidate252_independent_audit as base
import permutation252_spare_fold_search as boxes

def load_strict():
    p=ROOT/'agents/machine_reduction/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    sys.modules['cost_search']=SimpleNamespace()
    spec=importlib.util.spec_from_file_location('mixed_box_strict',p)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    return m,p

def cases(strict):
    p=ROOT/'agents/machine_reduction/Prog254.v'
    source=p.read_text().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',source)
    assert len(nodes)==6459
    out=[]
    def visit(q,path):
        for b,e in enumerate(nodes[q]):
            pc=path+str(b);op,*args=e.split()
            if op=='CN':visit(int(args[0]),pc);continue
            r=int(args[0]) if args else None
            for zero in ((True,False) if op=='CD' else (None,)):
                physical=base.NEWPHYS[r] if op in ('CI','CD') else r
                branch=(physical,zero) if op=='CD' else None
                nxt=base.successor(pc,op,r,zero)
                effect=('inc',physical) if op=='CI' else ('dec',physical) if op=='CD' and not zero else None
                right=[('b',int(b)) for b in nxt] if nxt is not None else []
                right += [('r',0,1,(41 if nxt is None else 40)-len(nxt or '')),('b',1),('box',('plain',effect))]
                out.append((pc,branch,strict.canon([('b',1)],right),op=='CH'))
    visit(0,'');assert len(out)==8391
    return out,p

class Track(dict):
    def __init__(self,t):super().__init__(t);self.used=set()
    def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=ROOT/'experiments/mixed_box_results.json')
    ap.add_argument('--seconds',type=float,default=600)
    ap.add_argument('--fuel',type=int,default=1000)
    args=ap.parse_args()
    if not __debug__:ap.error('Assertions required')
    path=ROOT/'sources/candidate-permutation252/zfc_permutation252_old.tm'
    raw=path.read_bytes();assert hashlib.sha256(raw).hexdigest()==base.EXPECTED_SHA
    table=base.read_table(raw);ss=list(boxes.samples());assert len(ss)==540
    usage=[]
    for c in ss:
        ok,reason,used,ticks=boxes.run(table,c,args.fuel)
        assert ok,reason
        usage.append(used)
    targets={table[k][2] for k in base.BOX_PAIRS}
    deadstates=sorted((base.BOX_STATES|targets)-{64,96})
    assert len(deadstates)==29
    states=sorted({q for q,b in table})
    # Mixed orientation: only one row of the retained state is copied; all
    # references to the deleted label, including in that copied row, relocate.
    recipes=[]
    for dead in deadstates:
        for keep in states:
            if keep==dead or keep in (64,96):continue
            for bit in (0,1):
                if table[dead,bit]==table[keep,bit]:continue
                recipes.append((dead,keep,bit))
    result=dict(scope='Finite literal boxes with existential valid spares; conditional affine screening only. No smaller consistency machine claim.',
        attribution='Mira-Cult, Jeff, Wade, mira-emmy and ProveIt permutation252; box samples from pinned ProveIt spare-fold search.',
        frozen_sha256=base.EXPECTED_SHA,baseline_samples=540,planned=len(recipes),tested=0,
        literal_samples=0,failures=[],box_survivors=[],affine_results=[],fuel=args.fuel)
    start=time.monotonic();reasons=Counter()
    for dead,keep,bit in recipes:
        if time.monotonic()-start>=args.seconds:break
        current={k:(w,d,keep if t==dead else t) for k,(w,d,t) in table.items() if k[0]!=dead}
        w,d,t=table[dead,bit];current[keep,bit]=(w,d,keep if t==dead else t)
        assert len(current)==502 and all(t!=dead for w,d,t in current.values())
        affected={(keep,bit)}|{k for k,v in table.items() if k[0]==dead or v[2]==dead}
        order=sorted(range(len(ss)),key=lambda i:not bool(usage[i]&affected))
        for i in order:
            ok,reason,used,ticks=boxes.run(current,ss[i],args.fuel,dead,keep)
            result['literal_samples']+=1
            if not ok:
                result['failures'].append([dead,keep,bit,i,reason,ticks]);reasons[reason]+=1;break
        else:result['box_survivors'].append([dead,keep,bit])
        result['tested']+=1
        if result['tested']%1000==0:print('BOX',result['tested'],'/',len(recipes),'survivors',len(result['box_survivors']),flush=True)
    result['box_elapsed_seconds']=time.monotonic()-start
    result['failure_reasons']=dict(reasons)
    result['status']='complete' if result['tested']==result['planned'] else 'time_bound_partial'
    strict,strict_path=load_strict();cc,prog_path=cases(strict);oracle=strict.oracle
    ordinary={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in table.items()}
    instruction_usage=[]
    for pc,branch,target,halt in cc:
        traced=Track(ordinary)
        rules,n=strict.run(traced,pc,branch,target,halt=halt,fuel=args.fuel)
        assert n>0
        instruction_usage.append(traced.used)
    result['affine_baseline']=8391
    for dead,keep,bit in result['box_survivors']:
        # A deleted macro entry can create ambiguous contracts after relocation.
        # These cases need a redesigned oracle and are kept explicitly open.
        if dead in base.SKIP or dead in (43,73):
            result['affine_results'].append(dict(recipe=[dead,keep,bit],status='macro_entry_relocation_requires_new_contract'));continue
        def relocated(q,branch,state):
            answer=oracle(q,branch,state)
            if answer is None:return None
            out,effect=answer
            return (str(keep) if out==str(dead) else out),effect
        strict.oracle=relocated
        current={k:(w,d,str(keep) if t==str(dead) else t) for k,(w,d,t) in ordinary.items() if k[0]!=str(dead)}
        w,d,t=ordinary[str(dead),bit];current[str(keep),bit]=(w,d,str(keep) if t==str(dead) else t)
        affected={(str(keep),bit)}|{k for k,v in ordinary.items() if k[0]==str(dead) or v[2]==str(dead)}
        order=sorted(range(len(cc)),key=lambda i:not bool(instruction_usage[i]&affected))
        passed=0
        for i in order:
            pc,branch,target,halt=cc[i]
            try:
                rules,n=strict.run(current,pc,branch,target,halt=halt,fuel=args.fuel)
                assert n>0;passed+=1
            except (AssertionError,KeyError) as ex:
                result['affine_results'].append(dict(recipe=[dead,keep,bit],status='checker_rejection',passed=passed,case=i,error=str(ex)));break
        else:
            result['affine_results'].append(dict(recipe=[dead,keep,bit],status='conditional_pass',passed=passed))
            print('CONDITIONAL SURVIVOR',dead,keep,bit,flush=True)
    strict.oracle=oracle
    result['elapsed_seconds']=time.monotonic()-start
    result['input_sha256']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [path,strict_path,prog_path,Path(base.__file__),Path(boxes.__file__),Path(__file__)]}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','planned','tested','literal_samples','box_survivors','elapsed_seconds']},indent=2),flush=True)

if __name__=='__main__':main()
