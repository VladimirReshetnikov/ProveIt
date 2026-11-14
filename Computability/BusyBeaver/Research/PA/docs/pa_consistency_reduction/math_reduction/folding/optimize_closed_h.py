#!/usr/bin/env python3
"""Run closed-chunk optimization against the validated h-only Shift variant."""
from pathlib import Path
import json,time
import optimize_closed as O
O.ORIGINAL=O.S.load_machine(O.W/'comparison/audit/h_catalan_node170_3_133_37.tm')
O.BASE={k:v for k,v in O.ORIGINAL.items() if k[0]<134}
r=O.RAW
n168=(r['node167'],r['node145']);n169=(r['node36'],n168);n170=(n169,r['node57'])
O.ROOT=(r['node21'],(n170,r['node23']))
original_sites=O.S.flatten(O.ROOT);original_codes=O.S.instructions(original_sites)
assert len(original_sites)==3811
old_output=O.output
def output(t,path):
    path=path.with_name(path.stem+'_h'+path.suffix)
    old_output(t,path)
    d=json.loads(path.read_text());d['variant']='h-only Shift';path.write_text(json.dumps(d,indent=2))
O.output=output

def validate(t,path):
    m,new,entry=O.make(t);score,n,c,sel=O.evaluate(t);mm,mu=O.F.fold(m,sel)
    newtree=O.C.replace(O.ROOT,O.RAW['x67'],O.raw(t));sites=O.S.flatten(newtree)
    assert len(sites)==3811
    old=O.S.all_sites;O.S.all_sites=lambda:sites
    failures=[];lens=[]
    try:
        assert O.S.check_engine(mm)
        for i,branch,br,initial,target in O.S.contracts():
            v=O.S.execute(mm,br,initial,target)
            if v is None:failures.append((i,branch))
            else:lens.append(v[0])
    finally:O.S.all_sites=old
    result=dict(states=len(mm)//2,sites=len(sites),unchanged_instructions=O.S.instructions(sites)==original_codes,
        max_path=max(len(p) for p,op in sites),passed=len(lens),failures=failures,max_symbolic=max(lens,default=0))
    path=path.with_name(path.stem+'_h'+path.suffix)
    path.with_suffix('.tm').write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(mm.items())))
    path.with_suffix('.check.json').write_text(json.dumps(result,indent=2))
    path.with_suffix('.sites.json').write_text(json.dumps(sites))
    return result
O.validate=validate
if __name__=='__main__':O.main()
