#!/usr/bin/env python3
"""Consume a unary counter while comparing a biased, once-marked unary field.
Prepared-frame binary TM component, not a complete consistency machine.
"""
if not __debug__: raise RuntimeError('Assertions required')
from pathlib import Path
import itertools, random, json, hashlib
OUT=Path(__file__).resolve().parent

def compile_compare(fold=True):
    rows={}
    def p(q,b,w,d,t):
        assert (q,b) not in rows
        rows[q,b]=(w,d,t)
    p('init',0,1,'R','erase_first')
    p('erase_first',1,0,'R','erase_second')
    p('erase_second',1,0,'R','next_source')
    p('next_source',1,0,'L','back_one')
    p('next_source',0,0,'L','restore_right')
    p('back_one',0,0,'L','restore_old_left')
    p('restore_old_left',0,1,'L','loop_ones')
    for mode,cont in [('loop','decrement'),('done','done_check'),('failed','clear_counter')]:
        p(mode+'_ones',1,1,'L',mode+'_ones')
        p(mode+'_ones',0,0,'L',mode+'_zero')
        p(mode+'_zero',1,1,'L',mode+'_ones')
        p(mode+'_zero',0,0,'L',mode+'_gap')
        p(mode+'_gap',0,0,'L',mode+'_gap')
        if mode=='loop':p(mode+'_gap',1,0,'L',cont)
        elif mode=='done':p(mode+'_gap',1,1,'L',cont)
        else:p(mode+'_gap',1,0,'L',cont)
    p('decrement',1,1,'R','gap_right')
    p('decrement',0,0,'R','restore_exhausted')
    p('restore_exhausted',0,1,'R','failed_gap_right')
    for mode in ('','failed_'):
        p(mode+'gap_right',0,0,'R',mode+'gap_right')
        p(mode+'gap_right',1,1,'R',mode+'find_ones')
        p(mode+'find_ones',1,1,'R',mode+'find_ones')
        p(mode+'find_ones',0,0,'R',mode+'find_first')
        p(mode+'find_first',1,1,'R',mode+'find_ones')
    p('find_first',0,0,'R','next_source')
    p('failed_find_first',0,1,'L','failed_restore_left')
    p('failed_restore_left',0,1,'L','failed_ones')
    p('restore_right',0,1,'L','restore_left')
    p('restore_left',0,1,'L','done_ones')
    p('done_check',0,0,'R','EQ')
    p('done_check',1,1,'R','clear_counter')
    p('clear_counter',1,0,'L','clear_counter')
    p('clear_counter',0,0,'R','restore_counter')
    p('restore_counter',0,1,'R','return_neq')
    p('return_neq',0,0,'L','NEQ')
    names=list(dict.fromkeys(q for q,b in rows))
    forced={q:sorted(b for name,b in rows if name==q) for q in names}
    aliases={}
    if fold:
        # Each pair's valid-read sets are disjoint; initialization sees one,
        # whereas the respective restoring/returning operation sees zero.
        aliases={'erase_first':'return_neq','erase_second':'restore_counter'}
    def rename(q):return aliases.get(q,q)
    new={}
    for (q,b),(w,d,t) in rows.items():
        k=(rename(q),b);assert k not in new
        new[k]=(w,d,rename(t))
    names=list(dict.fromkeys(rename(q) for q in names))+['reject']
    names=list(dict.fromkeys(names))
    ids={q:i for i,q in enumerate(names)}
    ports={'EQ':len(names),'NEQ':len(names)+1}
    for q in names:
        for b in (0,1):
            if(q,b)not in new:new[q,b]=(b,'R','reject')
    table={(ids[q],b):(w,d,ports[t]if t in ports else ids[t])for(q,b),(w,d,t)in new.items()}
    return table,ids['init'],ports,ids,aliases,forced

def header(k):
    assert 1<=k<=4
    return '1'*k+'0'+'1'*(5-k)+'0'

def frame(a,b,other,i,gap=2,c=0,k=1):
    assert a>=0 and b>=0 and gap>=2 and 0<=i<=len(other)
    vals=other[:i]+[b+3]+other[i:]
    assert all(v>=1 for v in vals)
    h=c+a+gap+1;ones=set(range(c,c+a+1))
    ones|={h+j for j,v in enumerate(header(k))if v=='1'}
    p=h+7;starts=[]
    for v in vals:
        starts.append(p);ones.update(range(p,p+v));p+=v+1
    s=starts[i];ones.remove(s)
    return ones,s,p,h

def execute(T,start,ports,ones,h,limit=10000000):
    ones=set(ones);q=start;steps=0;lo=hi=h;reads=set()
    while q not in ports.values():
        assert steps<limit,('fuel',q,h,steps)
        lo=min(lo,h);hi=max(hi,h);b=int(h in ones);reads.add((q,b))
        w,d,q=T[q,b]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R'else-1;steps+=1
    return ones,h,next(k for k,v in ports.items()if v==q),steps,(lo,hi),reads

def check(T,start,ports,a,b,other,i,gap=2,c=0,k=1,ext=()):
    original,s,e,h=frame(a,b,other,i,gap,c,k);original|=set(ext)
    assert c-1 not in original
    wanted=(original-set(range(c+1,c+a+1)))|{s}
    out,head,port,n,window,reads=execute(T,start,ports,original,s)
    assert out==wanted,('tape',a,b,other,i,gap,k,sorted(out^wanted))
    assert head==c and port==('EQ'if a==b else'NEQ'),('return',a,b,head,c,port)
    assert window[0]>=c-1 and window[1]<=s+b+3,('window',window,c,s,b)
    return n,reads

def main():
    T,s,P,ids,aliases,forced=compile_compare();count=0;maxsteps=0;used=set()
    for a,b,i,gap,k in itertools.product(range(8),range(8),range(4),(2,3,8),range(1,5)):
        n,r=check(T,s,P,a,b,[1,2,5],i,gap,k=k);count+=1;maxsteps=max(maxsteps,n);used|=r
    rng=random.Random(202610180337)

    for trial in range(2000):
        a=rng.randrange(100);b=rng.randrange(100);other=[rng.randrange(1,30)for _ in range(rng.randrange(20))];i=rng.randrange(len(other)+1)
        gap=rng.randrange(2,30);c=rng.randrange(-50,51);k=rng.randrange(1,5)
        _,ss,end,hh=frame(a,b,other,i,gap,c,k)
        ext=[c-j for j in range(2,20)if rng.randrange(2)]+[end+j for j in range(20)if rng.randrange(2)]
        n,r=check(T,s,P,a,b,other,i,gap,c,k,ext);count+=1;maxsteps=max(maxsteps,n);used|=r
    text='# Prepared-frame comparator; separate EQ/NEQ ports '+json.dumps(P)+'\n#! start '+str(s)+'\n'+''.join(f'{q} {b} {w} {d} {t}\n'for(q,b),(w,d,t)in sorted(T.items()))
    (OUT/f'compare_biased_counter_{len(ids)}.tm').write_text(text)
    result=dict(status='PASS',scope='Prepared-frame unary equality with destructive counter and fully restored source/header; no full-machine claim',states=len(ids),operational_states=len(ids)-1,ports=P,start=s,names=ids,folds=aliases,pre_fold_valid_reads=forced,tests=count,maximum_steps=maxsteps,table_sha256=hashlib.sha256(text.encode()).hexdigest(),observed_reads={name:sorted(b for q,b in used if q==i)for name,i in ids.items()})
    (OUT/'compare_biased_counter_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
