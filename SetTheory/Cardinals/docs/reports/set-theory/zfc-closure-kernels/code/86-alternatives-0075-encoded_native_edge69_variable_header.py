#!/usr/bin/env python3
"""Single-entry native edge step with biased pointers and in-tape mode.

Each record is tag 1^(t+1)0, left 1^(L+3)0, right 1^(R+3)0.
The current record's first tag1 is erased. A unary counter1 sits at c; after
a blank gap >= selected_reference+2 the anchor is 1^(1+2*b+e)0. Its length
supplies branch b and expected tag bit e. Start and return on the erased tag
cell. Exact result: only this marker moves to referenced record L or R.

The machine reads its mode itself and charges every marker/copy/reset/return
state. It does not produce that mode from template queries or enumerate proofs.
"""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import sys,random,itertools,json,hashlib
import pattern_oracle as O
import unary_locator as L
import tag_edge as E
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'native_copier'))
import biased_reference_copy as C


def compile_step():
    et,ee,er,ej,en=E.compile_edge();ct,ce,cr,ci=C.compile_copy();lt=L.compile_locator()
    edrop={en.index('return_right')};cdrop={ci['init_bias']}
    specs=[('edge',et,er,ej,edrop),('copy',ct,cr,ci['reject'],cdrop),('loc',lt,L.RETURN,L.IDS['reject'],set())]
    ids={};names=[]
    for pref,table,ret,reject,drop in specs:
        for q in range(ret):
            if q!=reject and q not in drop:ids[pref,q]=len(names);names.append((pref,q))
    extra=['reset_leave','reset_gap','reset_anchor','reset_mark','return_marker','reject',
      'fetch','skip_separator','left_ones','left_zero','to_anchor',
      *[('anchor',k) for k in range(1,5)],*[('find_ones',b,e) for b,e in ee]]
    for n in extra:ids[n]=len(names);names.append(n)
    ret=len(names);reject=ids['reject'];out={}
    for pref,table,oldret,oldreject,drop in specs:
        for (q,b),(w,d,q2) in table.items():
            if q==oldreject or q in drop:continue
            if pref=='edge' and en[q]=='mark_child' and b==1:
                # No need to erase/restore the source first1. Enter the biased
                # copy directly one cell to its right, skipping both adapters.
                out[ids[pref,q],b]=(1,'R',ids['copy',ci['erase_first']]);continue
            if q2==oldreject:dest=reject
            elif q2==oldret:
                dest={'copy':ids['reset_leave'],'loc':ids['return_marker']}.get(pref,ret)
            else:dest=ids[pref,q2]
            out[ids[pref,q],b]=(w,d,dest)
    # Variable-length nonempty anchor is still a single unary field.
    for q in (L.IDS['anchor_advance'],L.IDS['anchor_done']):out[ids['loc',q],1]=(1,'R',ids['loc',q])
    out[ids['copy',ci['after_anchor']],1]=(1,'R',ids['copy',ci['after_anchor']])
    def p(q,b,w,d,n):out[ids[q],b]=(w,d,ret if n=='RETURN' else ids[n])
    for b in range(2):
        p('reset_leave',b,b,'R','reset_gap');p('return_marker',b,b,'L','RETURN');p('reject',b,b,'R','reject')
    p('reset_gap',0,0,'R','reset_gap');p('reset_gap',1,1,'R','reset_anchor')
    p('reset_anchor',0,0,'R','reset_mark');p('reset_anchor',1,1,'R','reset_anchor')
    p('reset_mark',1,0,'L',('loc',L.IDS['return_ones']));p('reset_mark',0,0,'R','reject')
    p('fetch',0,0,'L','skip_separator');p('fetch',1,1,'R','reject')
    for b in range(2):p('skip_separator',b,b,'L','left_ones')
    p('left_ones',1,1,'L','left_ones');p('left_ones',0,0,'L','left_zero')
    p('left_zero',1,1,'L','left_ones');p('left_zero',0,0,'R','to_anchor')
    p('to_anchor',0,0,'R','to_anchor');p('to_anchor',1,1,'R',('anchor',1))
    for k in range(1,5):
        mode=((k-1)//2,(k-1)%2)
        p(('anchor',k),0,0,'R',('edge',ee[mode]))
        p(('anchor',k),1,1,'R',('anchor',k+1) if k<4 else 'reject')
    for (b,e),q in ee.items():
        # Reuse the 4 existing marker-entry states as first-field scanners.
        out[ids['edge',q],1]=(1,'R',ids['find_ones',b,e])
        p(('find_ones',b,e),1,1,'R',('find_ones',b,e))
        p(('find_ones',b,e),0,0,'R',('edge',q))
    assert len(out)==2*ret and ret==69
    return out,ids['fetch'],ret,reject,names


def frame(records,selected,branch,e,gap,c=0):
    assert gap>=records[selected][1+branch]+2
    tape={c:1};anchor=c+gap+1
    for j in range(1+2*branch+e):tape[anchor+j]=1
    x=anchor+(1+2*branch+e)+1;starts=[]
    for tag,left,right in records:
        starts.append(x)
        for v in (tag,left+2,right+2):
            for p in range(x,x+v+1):tape[p]=1
            x+=v+2
    tape.pop(starts[selected]);return tape,starts,x


def run(t,start,ret,reject,tape,h,limit=4000000):
    tape=dict(tape);q=start;steps=0
    while q not in (ret,reject):
        if steps>=limit:raise RuntimeError(('fuel',q,h))
        w,d,q=t[q,tape.get(h,0)]
        if w:tape[h]=w
        else:tape.pop(h,None)
        h+=1 if d=='R' else -1;steps+=1
    return q==ret,tape,h,steps


def check(t,start,ret,reject,records,selected,branch,e,gap):
    tape,starts,end=frame(records,selected,branch,e,gap);tape[-3]=1;tape[end+2]=1
    ok,actual,h,steps=run(t,start,ret,reject,tape,starts[selected])
    assert ok==((records[selected][0]>>branch)&1==e)
    if ok:
        child=records[selected][1+branch];want=dict(tape);want[starts[selected]]=1;want.pop(starts[child])
        assert actual==want,(records,selected,branch,sorted(set(actual)^set(want)))
        assert h==starts[child]
    return ok,steps


def main():
    t,start,ret,reject,names=compile_step();tests=accepted=max_steps=0;rng=random.Random(6924618);cases=[]
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
            ok,steps=check(t,start,ret,reject,records,selected,branch,e,gap)
            tests+=1;accepted+=ok;max_steps=max(max_steps,steps)
    p=Path(__file__).parent/f'encoded_native_edge_{ret}.tm';O.save_table(p,t,ret,start)
    result={'scope':'Single-entry prepared-frame native edge step with in-tape mode, not complete template/proof checker',
      'working_states':ret,'transition_rows':len(t),'start':start,'separate_return':ret,
      'composition':{'tag_check_and_child_start':14,'biased_copy_without_first_cell_adapter':19,
       'locator':17,'record_reset':4,'head_return':1,'mode_fetch_and_marker_seek':13,'shared_reject':1},
      'tests':tests,'accepted':accepted,'max_steps':max_steps,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
    (p.parent/'encoded_native_edge_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
