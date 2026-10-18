#!/usr/bin/env python3
"""Price a changed decoder through source27's literal contextual emitter.

Affine runtime verification is conditional on the four unchanged Box routines.
The input register program's mathematical equivalence is a separate obligation.
"""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, sys, time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent/'ProveIt'
sys.path.insert(0,str(HERE/'grammar_search'))
sys.path.insert(0,str(ROOT/'Computability/BusyBeaver/Research/ZFC'))
import cost_search as source
import strict_affine as strict
import candidate252_independent_audit as audit

class Tracking(dict):
    def __init__(self,table):super().__init__(table);self.used=set()
    def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)

def normalize(data):
    return {int(k):tuple(map(tuple,v)) for k,v in data['nodes'].items()},int(data['root'])

def table_for(nodes,root,scan8=False):
    original=source.emit(nodes,root)
    table={k:(w,d,'64' if t=='5' else t) for k,(w,d,t) in original.items() if k[0]!='5'}
    for q,b in audit.SELECTOR_INCOMING:
        k=str(q),b;w,d,t=table[k]
        table[k]=w,d,str(audit.SKIP[audit.PERM[audit.SKIP.index(int(t))]])
    if scan8:
        table={k:(w,d,'84' if t=='74' else t) for k,(w,d,t) in table.items() if k[0]!='74'}
    assert all(table[str(q),b]==tuple((v if i!=2 else str(v)) for i,v in enumerate(audit.read_table((ROOT/'lib/jeff-busy-beaver-zfc254/ZF/m254/machine/zfc_254.tm').read_bytes())[q,b])) for q,b in audit.BOX_PAIRS)
    return table

def runtime_price(nodes,root,scan8=False):
    began=time.monotonic();table=table_for(nodes,root,scan8);tracked=Tracking(table)
    sites=source.sites(nodes,root);cases=0;cost=Counter();minimum=10**9
    for p,op,r in sites:
        for zero in ((True,False) if op=='CD' else (None,)):
            physical=audit.PERM[r] if op in ('CI','CD') else r
            branch=(physical,zero) if op=='CD' else None
            nxt=audit.successor(p,op,r,zero)
            effect=('inc',physical) if op=='CI' else ('dec',physical) if op=='CD' and not zero else None
            right=[('b',int(c)) for c in (nxt or '')]
            right += [('r',0,1,(41 if nxt is None else 40)-len(nxt or '')),('b',1),('box',('plain',effect))]
            try:
                counts,literal=strict.run(tracked,p,branch,strict.canon([('b',1)],right),halt=op=='CH',fuel=1500)
                assert literal>0
            except (KeyError,AssertionError) as e:
                return {'status':'affine_failure','case':cases,'path':p,'operation':op,'physical':physical,'zero':zero,'message':str(e),'decoder_nodes':len(nodes),'scan8':scan8,'elapsed_seconds':time.monotonic()-began},None
            cases+=1;cost.update(counts);minimum=min(minimum,literal)
    protected={(str(q),b) for q,b in audit.BOX_PAIRS}
    used=tracked.used|protected
    retained={q for q,b in used}|{'96','64'}
    pruned={}
    for k,(w,d,t) in table.items():
        if k[0] not in retained:continue
        if t not in retained|{'254'}:
            assert k not in used
            t='64'
        pruned[k]=w,d,t
    assert len(pruned)==2*len(retained)
    assert all(pruned[k]==table[k] for k in protected)
    return {'status':'affine_pass','decoder_nodes':len(nodes),'shape':source.rot.zero_metrics(nodes,root),'scan8':scan8,
        'cases':cases,'sites':len(sites),'minimum_literal_steps':minimum,'table_states_before_pruning':len(table)//2,
        'runtime_working_states':len(pruned)//2,'elapsed_seconds':time.monotonic()-began,'rule_counts':dict(cost)},pruned

def write_table(path,table):
    data='#! start 64\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(table.items(),key=lambda x:(int(x[0][0]),x[0][1])))
    path.write_text(data);return hashlib.sha256(data.encode()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input',type=Path)
    ap.add_argument('--scan8',action='store_true')
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();data=json.loads(args.input.read_text())
    candidates=data.get('short_zero_layouts',[data]);answers=[]
    for i,candidate in enumerate(candidates):
        nodes,root=normalize(candidate)
        answer,table=runtime_price(nodes,root,args.scan8)
        answer['index']=i
        if table:
            path=args.output.with_suffix(f'.{i}.tm')
            answer['table_sha256']=write_table(path,table);answer['table']=str(path)
        answers.append(answer);print(answer,flush=True)
    args.output.write_text(json.dumps({'scope':__doc__,'input':str(args.input),'input_sha256':hashlib.sha256(args.input.read_bytes()).hexdigest(),'answers':answers},indent=2)+'\n')

if __name__=='__main__':main()
