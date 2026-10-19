#!/usr/bin/env python3
"""135-state oracle/locator pipeline retaining the oracle output boundary.

The added state writes1 on the first unused query-buffer cell. All later buffer
cells remain0 and one0 immediately precedes the index counter even at depth23.
Thus the boundary is the rightmost1 strictly left of the counter separator.
The original branch path is still destroyed and must be retained separately.
"""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import json,hashlib
import integrated_oracle_locator as I
import pattern_oracle as O
import unary_locator as L


def compile_pipeline():
    old,start,oldret,o=I.compile_pipeline();mark=oldret;ret=oldret+1;seek=o['halt']+L.RETURN
    table={k:(w,d,ret if q==oldret else mark if k[0]<o['halt'] and q==seek else q)
           for k,(w,d,q) in old.items()}
    table[mark,0]=(1,'R',seek);table[mark,1]=(1,'R',o['halt']+L.IDS['reject'])
    assert len(table)==2*ret and ret==135
    return table,start,ret,o


def main():
    t,s,ret,o=compile_pipeline();cases=0;maxsteps=0;records=[(0,0,0),(1,0,0),(2,0,1),(3,2,2),(0,1,3)]
    for rule in o['roots']:
        for path,observed,leaf in O.enumerate_leaf_paths(o,rule):
            for i in range(len(records)):
                initial,starts,offset=I.make_frame(rule,path,i,records)
                actual,h,steps=I.run(t,s,ret,initial)
                want,wh,_=I.run(*I.compile_pipeline()[:3],initial)
                boundary=4+len(path)+3;want[boundary]=1
                assert actual==want and h==wh
                # Original counter left edge32 survives; its left neighbor is0.
                assert actual.get(31,0)==0 and actual.get(32,0)==1
                p=31
                while not actual.get(p,0):p-=1
                assert p==boundary
                cases+=1;maxsteps=max(maxsteps,steps)
    p=Path(__file__).parent/f'bounded_oracle_locator_{ret}.tm';O.save_table(p,t,ret,s)
    path,_,_=next(O.enumerate_leaf_paths(o,3));initial,_,_=I.make_frame(3,path,2,records[:3])
    bits=[initial.get(i,0) for i in range(max(initial)+1)];bt,bs,bh=I.add_blank_initializer(t,s,ret,bits)
    actual,h,steps=I.run(bt,bs,bh,{});want,wh,ws=I.run(t,s,ret,initial);shift=1-len(bits)
    assert actual=={i+shift:v for i,v in want.items()} and h==wh+shift
    bp=p.parent/f'blank_bounded_pipeline_probe_{bh}.tm';O.save_table(bp,bt,bh,bs)
    result={'scope':'Prepared-frame root selection, oracle, retained boundary, and indexed lookup; not complete proof search',
      'working_states':ret,'rows':len(t),'added_boundary_states':1,'tests':cases,'max_steps':maxsteps,
      'table_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
      'blank_probe':{'working_states':bh,'initializer_states':len(bits)+1,'steps':steps,'purpose':'Always-halting component demonstration'},
      'blank_sha256':hashlib.sha256(bp.read_bytes()).hexdigest()}
    (p.parent/'bounded_pipeline_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
