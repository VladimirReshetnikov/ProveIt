#!/usr/bin/env python3
"""Reach the offendingCI8 frame on the actual reference blank run.

The mutant is tested from that reached frame. Its own blank initialization is
not claimed. The one-entry repair experiment remains finite and bounded.
"""
from pathlib import Path
import argparse,json,hashlib
import check_runtime_variants as c
l=c.lit;ROOT=c.ROOT

def step(table,q,h,one):
    w,d,q=table[q,int(h in one)]
    one.add(h) if w else one.discard(h)
    return q,h+d

def run_to(table,q,h,one,goal,fuel=20000):
    for tick in range(1,fuel+1):
        q,h=step(table,q,h,one)
        assert q!=254,'Unexpected halt before required source frame'
        if (q,h,one)==goal:return q,h,one,tick
    raise AssertionError('Required source frame not reached')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--search-entry',action='store_true');ap.add_argument('--output',type=Path,default=ROOT/'reachable-prefix-left-verification.json');a=ap.parse_args()
    if not __debug__:raise SystemExit('Assertions required')
    ref=c.load('reference246_old.tm');mut=c.load('partial_prefix_left245_old.tm')
    q,h,one=95,0,set()
    for _ in range(410735):
        assert q!=254
        q,h=step(ref,q,h,one)
    regs=[0,0,0,3,0,0,3,0,0];spares=[1]*167;pc='';span=181
    assert (q,h,one)==(96,-5,l.paint(pc,span,regs,spares,-5))
    frames=[dict(label='reviewed_root',blank_steps=410735,head=h,pc=pc,span=span,physical_registers=regs.copy(),ones=sorted(one))]
    absolute=410735
    for path,kind,r in [('000','CD',8),('0100','CD',0)]:
        assert one==l.paint(path,span,regs,spares,h)
        out=l.expected(path,kind,r,regs,spares,h,span)
        q,h,one,ticks=run_to(ref,q,h,one,(96,out[0],out[1]))
        absolute+=ticks;pc=out[2];span=out[3];regs=out[4]
        frames.append(dict(label=kind+str(r),steps=ticks,blank_steps=absolute,head=h,pc=pc,span=span,physical_registers=regs.copy(),ones=sorted(one)))
    assert pc=='0101' and span==182 and regs==[0,0,0,3,0,0,2,0,0]
    assert one==l.paint('01010',span,regs,spares,h)
    source=(q,h,one.copy());updated=regs.copy();updated[l.PHYSICAL[8]]+=1
    exits={}
    for name,t in [('reference246',ref),('prefix_left245',mut)]:
        q,h,initial=source;one=initial.copy();seen=False;entry=None
        for tick in range(1,20001):
            if q==73 and not seen:seen=True;entry=dict(steps=tick-1,head=h)
            q,h=step(t,q,h,one)
            assert q!=254
            if seen and q==96:
                path2,span2,spares2=('01011',182,spares+[1]) if name=='reference246' else ('011',181,spares)
                assert h==-5 and one==l.paint(path2,span2,updated,spares2,h)
                exits[name]=dict(steps=tick,head=h,pc=path2,span=span2,spare_count=len(spares2),physical_registers=updated.copy(),ones=sorted(one),increment_entry=entry)
                break
        else:raise AssertionError('No post-increment dispatch')
    assert exits['reference246']['steps']==2590 and exits['prefix_left245']['steps']==1544
    result=dict(status='PASS',scope='An exact reached reference-blank frame refutes the unchanged increment continuation of the245-state prefix-left variant; no mutant blank-run halting conclusion.',
      reference_sha256=c.SHA(ROOT/'reference246_old.tm'),mutant_sha256=c.SHA(ROOT/'partial_prefix_left245_old.tm'),
      source_frames=frames,offending_instruction=dict(consumed_path='01010',kind='CI',logical_register=8),post_increment=exits)
    if a.search_entry:
        q,h,initial=source;one=initial.copy()
        for prefix in range(20000):
            if (q,int(h in one))==(57,1):break
            q,h=step(mut,q,h,one)
        else:raise AssertionError('entry57/1 not reached')
        assert prefix==796
        cached=(q,h,one.copy());states=sorted({q for q,b in mut});want=l.paint('01011',181,updated,spares,-5)
        ledger=[];passing=[]
        for target in states:
            for written in (0,1):
                for direction in (-1,1):
                    trial=mut.copy();trial[57,1]=(written,direction,target)
                    q,h,initial=cached;one=initial.copy();outcome='fuel_limit'
                    for tick in range(prefix+1,20001):
                        q,h=step(trial,q,h,one)
                        if q==254:outcome='halt';break
                        if q==96 and h==-5 and one==want:
                            outcome='pass';passing.append([written,direction,target,tick]);break
                    ledger.append([written,direction,target,outcome,tick])
        assert len(ledger)==980 and not passing
        result['entry_search']=dict(row=[57,1],recipes=980,fuel=20000,common_unchanged_prefix=796,
          gate='The exact reached reference source frame; exact desired one-cell-left increment endpoint at anytick through20000.',
          passing=passing,ledger=ledger,finite_only=True)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',offending_frame_reference_blank_time=frames[-1]['blank_steps'],source_steps=[f.get('steps') for f in frames[1:]],
      baseline_increment=2590,mutant_increment=1544,entry_recipes=980 if a.search_entry else None),indent=2))
if __name__=='__main__':main()
