#!/usr/bin/env python3
"""Replay the four H-loop rotations with the inherited affine checker.

This is optional source research, distinct from the primary242 theorem.
The needed reference is recovered by ProveIt's recover_167.py.
"""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json,sys,time

def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--reference',type=Path,required=True)
    ap.add_argument('--baseline-table',type=Path,required=True)
    ap.add_argument('--source',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();assert __debug__
    assert digest(a.baseline_table)=='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
    assert digest(a.source)=='74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d'
    sys.path.insert(0,str(a.reference.resolve()/'code'))
    import build_routing_machine as B
    import parametric_prefix_affine as affine
    from review_affine_source import full_inc,full_strip
    T,start=B.rebuild.read_table(a.baseline_table)
    assert start==95 and len(T)==486 and T[142,0]==(0,'R',37)and T[142,1]==(1,'R',72)
    T[142,0]=(0,'R',72);T[142,1]=(1,'R',17)
    source=json.loads(a.source.read_text());assert len(source)==6455
    physical=[(p,o,B.rebuild.PHYSICAL[r]if o in ('CI','CD')else r)for p,o,r in source]
    expected=sum(2 if o=='CD'else 1 for p,o,r in source);assert expected==8386
    a.output.mkdir(parents=True,exist_ok=True)
    outtable=a.output/'h_rotation243_old.tm';outtable.write_text(B.rebuild.encode(T,95))
    txt={(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in T.items()}
    affine.PADDING=64;began=time.monotonic();count=0;rules=Counter();minimum=None
    for i,(p,op,r)in enumerate(physical):
        for zero in ((True,False)if op=='CD'else(None,)):
            branch=(r,zero)if op=='CD'else None
            extra=0;effect=None;overflow=False
            if op=='CI':nxt,overflow=full_inc(p);effect=('inc',r)
            elif op=='CD'and not zero:nxt,overflow=full_inc(p);effect=('dec',r);extra=1
            elif op=='CD':nxt,overflow=full_inc(full_strip(p,'0',1))
            elif op=='CB':nxt,overflow=full_inc(full_strip(p,'0',r))
            elif op=='CC':nxt=full_strip(p,'1',r)
            else:assert op=='CH';nxt=''
            right=[('b',int(b))for b in nxt]+[('r',0,1,64+extra+int(overflow)-len(nxt)),('b',1),('box',('plain',effect))]
            rc,steps=affine.run(txt,p,branch,affine.canon([('b',1)],right),halt=op=='CH',fuel=1000)
            assert steps>0
            minimum=steps if minimum is None else min(minimum,steps)
            rules.update(rc);count+=1
    assert count==expected
    result=dict(status='PASS_UNIVERSAL_AFFINE_CASES',source_leaves=len(source),cases=count,
        working_states=len(T)//2,frame_padding=64,minimum_literal_steps=minimum,rules=dict(rules),
        seconds=time.monotonic()-began,baseline_sha256=digest(a.baseline_table),
        logical_source_sha256=digest(a.source),table_sha256=digest(outtable),
        checker_sha256=digest(affine.__file__),driver_sha256=digest(__file__),
        limitation='Inherited affine runtime contracts; no separate expanded replay, bootstrap proof, or kernel endpoint for this auxiliary table. It saves four source leaves but no binary states.')
    (a.output/'affine-verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
