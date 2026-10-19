#!/usr/bin/env python3
"""19-state nondestructive unary-path to reversed raw-binary copier.

Tape: frontier1, at least n+2 blanks, anchor11111 0, branch fields1^(b+3)0.
Erase the last1 of the last branch field (or anchor for n=0). Entry at that
marker. The machine restores every source cell, writes reversed(branches) at
the initial frontier, appends a frontier1, and returns one cell left of it.
A mirrored template oracle can therefore begin immediately, reading root-first
while moving L. No prepared source construction or initial marker is free.
"""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import itertools,random,json,hashlib
import pattern_oracle as O


def compile_copy():
    names=['restore','payload1','payload2','optional','long_test',
      *[(role,b) for b in range(2) for role in ('mark_previous','left_ones','left_zero','gap_left')],
      'append','gap_right','find_ones','find_zero','finish_gap','reject']
    ids={q:i for i,q in enumerate(names)};ret=len(names);t={}
    def p(q,b,w,d,n):t[ids[q],b]=(w,d,ret if n=='RETURN' else ids[n])
    p('restore',0,1,'L','payload1')
    p('payload1',1,1,'L','payload2');p('payload2',1,1,'L','optional')
    p('optional',0,0,'L',('mark_previous',0));p('optional',1,1,'L','long_test')
    p('long_test',0,0,'L',('mark_previous',1));p('long_test',1,1,'L','finish_gap')
    for b in range(2):
        p(('mark_previous',b),1,0,'L',('left_ones',b))
        p(('left_ones',b),1,1,'L',('left_ones',b));p(('left_ones',b),0,0,'L',('left_zero',b))
        p(('left_zero',b),1,1,'L',('left_ones',b));p(('left_zero',b),0,0,'L',('gap_left',b))
        p(('gap_left',b),0,0,'L',('gap_left',b));p(('gap_left',b),1,b,'R','append')
    p('append',0,1,'R','gap_right')
    p('gap_right',0,0,'R','gap_right');p('gap_right',1,1,'R','find_ones')
    p('find_ones',1,1,'R','find_ones');p('find_ones',0,0,'R','find_zero')
    p('find_zero',1,1,'R','find_ones');p('find_zero',0,0,'L','restore')
    p('finish_gap',0,0,'L','finish_gap');p('finish_gap',1,1,'L','RETURN')
    for q in names:
        for b in range(2):
            if (ids[q],b) not in t:p(q,b,b,'R','reject')
    assert len(names)==19 and len(t)==38
    return t,ids['restore'],ret,ids


def frame(bits,gap,c=0):
    assert all(b in (0,1) for b in bits) and gap>=len(bits)+2
    tape={c:1};anchor=c+gap+1
    for p in range(anchor,anchor+5):tape[p]=1
    cursor=anchor+4;x=anchor+6;starts=[]
    for b in bits:
        starts.append(x)
        for p in range(x,x+b+3):tape[p]=1
        cursor=x+b+2;x+=b+4
    tape.pop(cursor);return tape,cursor,anchor,x,starts


def run(t,start,ret,tape,h,limit=2000000):
    tape=dict(tape);q=start;steps=0
    while q!=ret:
        if steps>=limit:raise RuntimeError(('fuel',q,h))
        w,d,q=t[q,tape.get(h,0)]
        if w:tape[h]=w
        else:tape.pop(h,None)
        h+=1 if d=='R' else -1;steps+=1
    return tape,h,steps


def check(t,s,ret,bits,gap,c=0):
    initial,cursor,a,end,_=frame(bits,gap,c);initial[c-3]=1;initial[end+4]=1
    want=dict(initial);want[cursor]=1
    for j,b in enumerate(reversed(bits)):
        if b:want[c+j]=b
        else:want.pop(c+j,None)
    want[c+len(bits)]=1
    actual,h,steps=run(t,s,ret,initial,cursor)
    assert actual==want,(bits,gap,sorted(set(actual)^set(want)))
    assert h==c+len(bits)-1
    return steps


def main():
    t,s,ret,ids=compile_copy();tests=0;maxsteps=0
    for n in range(9):
        for bits in itertools.product(range(2),repeat=n):
            for extra in (2,3,9):
                maxsteps=max(maxsteps,check(t,s,ret,bits,n+extra));tests+=1
    rng=random.Random(1923102)
    for i in range(1000):
        bits=[rng.randrange(2) for j in range(rng.randrange(80))]
        maxsteps=max(maxsteps,check(t,s,ret,bits,len(bits)+rng.randrange(2,30),rng.randrange(-30,31)));tests+=1
    _,_,templates=O.load_source();o=O.compile_oracle(templates);oracle_tests=0
    mirrored={k:(w,'L',q) for k,(w,d,q) in o['table'].items()}
    for rule in o['roots']:
        for path,expected,leaf in O.enumerate_leaf_paths(o,rule):
            initial,cursor,a,end,_=frame(path,len(path)+2)
            after,h,_=run(t,s,ret,initial,cursor)
            result,oh,_=run(mirrored,o['roots'][rule],o['halt'],after,h)
            word=expected+list(map(int,format(leaf,'03b')))
            for j,b in enumerate(word):assert result.get(h-j,0)==b
            assert oh==h-len(word)
            for p in range(a,end):assert result.get(p,0)==(1 if p==cursor else initial.get(p,0))
            oracle_tests+=1
    p=Path(__file__).parent/f'reverse_path_copy_{ret}.tm';O.save_table(p,t,ret,s)
    result={'scope':'Prepared-frame nondestructive path copier; mirrored oracle integration tested, not full proof machine',
      'working_states':ret,'operational_states':ret-1,'shared_reject':1,'tests':tests,
      'literal_mirrored_oracle_paths':oracle_tests,'max_steps':maxsteps,
      'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'states':{str(k):v for k,v in ids.items()}}
    (p.parent/'reverse_path_copy_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
