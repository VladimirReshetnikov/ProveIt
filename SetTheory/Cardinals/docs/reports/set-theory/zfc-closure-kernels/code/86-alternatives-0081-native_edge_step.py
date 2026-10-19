#!/usr/bin/env python3
"""Literal composition: check tag bit, copy child index, relocate marker.

The four entry ports receive a retained (branch, expected_bit) pair. Start on
the erased first tag cell of any selected record, with unary counter 1 and
sufficient blank gap. On success restore the old marker and mark the selected
child record, returning on its erased first tag cell. Everything else is exact.
Neither bit fetching nor template-path control is implemented by this module.
"""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import sys,random,itertools,json,hashlib
import pattern_oracle as O
import unary_locator as L
import tag_edge as E
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'native_copier'))
import marked_unary_copy as C


def compile_step():
    et,ee,er,ej,en=E.compile_edge();ct,ce,cr,ci=C.compile_copy();lt=L.compile_locator()
    specs=[('edge',et,er,ej),('copy',ct,cr,ci['reject']),('loc',lt,L.RETURN,L.IDS['reject'])]
    ids={};names=[]
    for pref,table,ret,reject in specs:
        for q in range(ret):
            if q!=reject:ids[pref,q]=len(names);names.append((pref,q))
    for n in ('reset_leave','reset_gap','reset_anchor','reset_mark','return_marker','reject'):
        ids[n]=len(names);names.append(n)
    ret=len(names);reject=ids['reject'];out={}
    for pref,table,oldret,oldreject in specs:
        for (q,b),(w,d,q2) in table.items():
            if q==oldreject:continue
            if q2==oldreject:dest=reject
            elif q2==oldret:
                dest={'edge':ids['copy',ce],'copy':ids['reset_leave'],'loc':ids['return_marker']}[pref]
            else:dest=ids[pref,q2]
            # Locator normally exits one cell right of marker. Make one left
            # adapter at that position return exactly on the marker.
            out[ids[pref,q],b]=(w,d,dest)
    for b in range(2):
        out[ids['reset_leave'],b]=(b,'R',ids['reset_gap'])
        out[ids['return_marker'],b]=(b,'L',ret)
        out[reject,b]=(b,'R',reject)
    out[ids['reset_gap'],0]=(0,'R',ids['reset_gap'])
    out[ids['reset_gap'],1]=(1,'R',ids['reset_anchor'])
    out[ids['reset_anchor'],0]=(0,'R',ids['reset_mark'])
    out[ids['reset_anchor'],1]=(1,'R',reject)
    out[ids['reset_mark'],1]=(0,'L',ids['loc',L.IDS['return_ones']])
    out[ids['reset_mark'],0]=(0,'R',reject)
    assert len(out)==2*ret and ret==67
    return out,{m:ids['edge',q] for m,q in ee.items()},ret,reject,names


def run(t,start,ret,reject,tape,h,limit=2000000):
    tape=dict(tape);q=start;steps=0
    while q not in (ret,reject):
        if steps>=limit:raise RuntimeError(('fuel',q,h))
        w,d,q=t[q,tape.get(h,0)]
        if w:tape[h]=w
        else:tape.pop(h,None)
        h+=1 if d=='R' else -1;steps+=1
    return q==ret,tape,h,steps


def check(t,entries,ret,reject,records,selected,branch,e,gap):
    tape,starts=L.frame(0,records,gap);tape[starts[0]]=1;tape.pop(starts[selected])
    tape[-3]=1;tape[max(tape)+7]=1
    ok,actual,h,steps=run(t,entries[branch,e],ret,reject,tape,starts[selected])
    tag=records[selected][0]
    assert ok==((tag>>branch)&1==e)
    if ok:
        child=records[selected][1+branch]
        want=dict(tape);want[starts[selected]]=1;want.pop(starts[child])
        assert actual==want,(records,selected,branch,sorted(set(actual)^set(want)))
        assert h==starts[child]
    return ok,steps


def main():
    t,entries,ret,reject,names=compile_step();tests=accepted=max_steps=0
    rng=random.Random(1026718)
    cases=[]
    for n in range(1,7):
        for tag in range(4):
            for a,b in itertools.product(range(n),repeat=2):
                records=[(tag,a,b)]*n
                for selected in {0,n//2,n-1}:cases.append((records,selected,n+2))
    for trial in range(2000):
        n=rng.randrange(1,35);records=[(rng.randrange(4),rng.randrange(n),rng.randrange(n)) for _ in range(n)]
        cases.append((records,rng.randrange(n),n+rng.randrange(2,40)))
    for records,selected,gap in cases:
        for branch,e in itertools.product(range(2),repeat=2):
            ok,steps=check(t,entries,ret,reject,records,selected,branch,e,gap)
            tests+=1;accepted+=ok;max_steps=max(max_steps,steps)
    p=Path(__file__).parent/f'native_edge_step_{ret}.tm';O.save_table(p,t,ret,entries[0,0])
    result={'scope':'Four-entry prepared-frame native child-edge step, not complete path verifier or proof search',
      'working_states':ret,'operational_states':ret-1,'shared_nonhalting_reject':1,
      'composition':{'tag_edge':15,'copier':29,'locator':17,'first_record_reset':4,'head_return_adapter':1,'shared_reject':1},
      'separate_return':ret,'entries':{str(k):v for k,v in entries.items()},'tests':tests,'accepted':accepted,
      'max_steps':max_steps,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
    (p.parent/'native_edge_step_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
