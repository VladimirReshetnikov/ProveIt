#!/usr/bin/env python3
"""Literal binary tag-observation checker and chosen-child marker.

Four entries correspond to retained branch bit b and oracle observation e.
Start on the erased first cell of a unary tag field 1^(t+1)0, followed by
nonempty left/right unary fields. Restore tag marker, check (t>>b)&1 == e,
then erase the first cell of the chosen child field and return on that cell.
Arena validation guarantees 0<=t<4. Failed observation uses a distinct reject
port (totalized here by a nonhalting loop), never the success return.
This component does not fetch the two bits, copy pointers, or advance a path.
"""
if not __debug__:raise RuntimeError('Assertions must be enabled')
import itertools,json,hashlib
from pathlib import Path


def compile_edge():
    modes={(b,e):sum(1<<t for t in range(4) if (t>>b)&1==e) for b,e in itertools.product(range(2),repeat=2)}
    tails={}
    for (b,e),m in modes.items():
        while m:
            tails[b,m]=None;m>>=1
    names=[('entry',b,e) for b,e in modes]+[('test',b,m) for b,m in sorted(tails)]+['skip_left','mark_child','return_right','reject']
    ids={n:i for i,n in enumerate(names)};ret=len(names);reject=ids['reject'];table={}
    def add(q,r,w,d,n):table[ids[q],r]=(w,d,ret if n=='RETURN' else ids[n])
    for (b,e),m in modes.items():
        add(('entry',b,e),0,1,'R',('test',b,m));add(('entry',b,e),1,1,'R','reject')
    for b,m in tails:
        add(('test',b,m),0,0,'R',('mark_child' if b==0 else 'skip_left') if m&1 else 'reject')
        add(('test',b,m),1,1,'R',('test',b,m>>1) if m>>1 else 'reject')
    add('skip_left',1,1,'R','skip_left');add('skip_left',0,0,'R','mark_child')
    add('mark_child',1,0,'L','return_right');add('mark_child',0,0,'R','reject')
    for b in range(2):
        add('return_right',b,b,'R','RETURN');add('reject',b,b,'R','reject')
    assert len(table)==2*ret
    return table,{mode:ids['entry',*mode] for mode in modes},ret,reject,names


def run(table,start,ret,reject,tape):
    tape=dict(tape);h=0;q=start;steps=0
    while q not in (ret,reject):
        w,d,q=table[q,tape.get(h,0)]
        if w:tape[h]=w
        else:tape.pop(h,None)
        h+=1 if d=='R' else -1;steps+=1
        assert steps<10000
    return q==ret,tape,h,steps


def main():
    table,entries,ret,reject,names=compile_edge();tests=0;accepted=0
    for t,a,b,branch,e in itertools.product(range(4),range(25),range(25),range(2),range(2)):
        tape={};x=0;starts=[]
        for v in (t,a,b):
            starts.append(x)
            for p in range(x,x+v+1):tape[p]=1
            x+=v+2
        tape.pop(0);tape[-7]=1;tape[x+9]=1
        ok,actual,h,steps=run(table,entries[branch,e],ret,reject,tape)
        assert ok==((t>>branch)&1==e)
        if ok:
            want=dict(tape);want[0]=1;want.pop(starts[branch+1]);assert actual==want
            assert h==starts[branch+1];accepted+=1
        tests+=1
    import pattern_oracle as O
    p=Path(__file__).parent/f'tag_edge_{ret}.tm';O.save_table(p,table,ret,entries[0,0])
    result={'scope':'Prepared-frame tag-bit checker and chosen-child marker, not full path traverser',
      'working_states':ret,'operational_states':ret-1,'totalizing_reject':reject,'separate_return':ret,
      'entries':{str(k):v for k,v in entries.items()},'tests':tests,'accepted':accepted,
      'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'states':list(map(str,names))}
    (p.parent/'tag_edge_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
