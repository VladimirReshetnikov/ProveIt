#!/usr/bin/env python3
"""Independent executable audit of Morita-Imai 2001 Thm 3.6.

Only intentional mathematical repair: scheme 8.2's output-center +gamma
is replaced by -gamma unless printed_82=True. Scheme 8.2 uses the TARGET
increment's counter, independent of the no-op quadruple's irrelevant counter.
The source final state m-1 is required to have no outgoing transition;
initial state 0 has no incoming transition. Delta entries (i,j,op,k).
"""
from itertools import product, combinations
from collections import defaultdict, Counter
import random, json, csv, hashlib
from pathlib import Path

ZERO=(0,0,0)
OPS=('+','-','0','Z','P')

def overlap(a,b,index):
    return a[index]==b[index] and (a[1]!=b[1] or a[2]==b[2] or a[2] in '+-0' or b[2] in '+-0')

def valid(m,delta, reversible=True):
    return (all(0<=i<m-1 and 0<=j<2 and op in OPS and 0<k<m for i,j,op,k in delta)
            and all(not overlap(a,b,0) and (not reversible or not overlap(a,b,3))
                    for a,b in combinations(delta,2)))

def metadata(m,delta):
    instruction={i:(op,j) for i,j,op,k in delta}
    gam=lambda i: {'+':2+4*instruction[i][1], '-':4+3*instruction[i][1]}.get(instruction[i][0],0) if i in instruction else 0
    inc=lambda i: instruction[i][1] if i in instruction and instruction[i][0]=='+' else None
    return instruction,gam,inc

def compile_partial(m,delta,printed_82=False):
    assert valid(m,delta)
    instruction,gam,inc=metadata(m,delta)
    rows=[]
    def add(a,b,label): rows.append((a,b,label))
    base=lambda i:m+16-(i+10)-gam(i)
    for x in range(m+19):add((0,x,0),(0,x,0),'1')
    for x in range(10,m+10):add((0,0,x),(0,0,x),'2')
    for j,c in product(range(2),repeat=2):
        v=2**j; w=c*2**(j^1); a=2+4*j; d=4+3*j
        add((a,w,0),(0,w,a),'3.1')
        add((a,v+w,0),(0,w,a+v),'3.2')
        add((a+v,w,0),(a,v+w,0),'3.3')
        add((0,w,a),(a,w,0),'3.4')
        add((d,w,0),(0,w,d),'4.1')
        add((d,v+w,0),(d+v,w,0),'4.2')
        add((0,w,d+v),(d,v+w,0),'4.3')
        add((0,w,d),(d,w,0),'4.4')
    for i,j,op,k in delta:
        I=i+10; K=k+10; G=gam(i); H=gam(k); J=inc(k)
        v=2**j; u=2**(j^1)
        if op in '+-':
            for c in range(2):add((I,base(i)+c*u,0),(I,base(i)+c*u,0),'5')
        if op=='+':
            for c in range(2):
                a=(I,base(i)+c*u,G)
                if J!=j^1: add(a,(K,base(k)+c*u,H),'6.1')
                else: add(a,(K,base(k),H+c*u),'6.2')
        elif op=='-':
            for c,d in product(range(2),repeat=2):
                a=(I,base(i)+d*u,G+c*v)
                if J is None:add(a,(K,base(k)+c*v+d*u,H),'7.1')
                elif J==j:add(a,(K,base(k)+d*u,H+c*v),'7.2')
                else:add(a,(K,base(k)+c*v,H+d*u),'7.3')
        elif op=='0':
            for c,d in product(range(2),repeat=2):
                if J is None:
                    add((I,base(i)+c+2*d,0),(K,base(k)+c+2*d,H),'8.1')
                else:
                    V=2**J; U=2**(J^1)
                    add((I,base(i)+c*V+d*U,0),(K,base(k)+d*U+(2*H if printed_82 else 0),H+c*V),'8.2')
        elif op=='Z':
            for c in range(2):
                a=(I,base(i)+v+c*u,0)
                if J is None:add(a,(K,base(k)+v+c*u,H),'9.1')
                elif J==j:add(a,(K,base(k)+c*u,H+v),'9.2')
                else:add(a,(K,base(k)+v,H+c*u),'9.3')
        elif op=='P':
            for c in range(2):
                a=(I,base(i)+c*u,0)
                if J!=j^1:add(a,(K,base(k)+c*u,H),'9.4')
                else:add(a,(K,base(k),H+c*u),'9.5')
    add((1,0,0),(0,0,1),'10.1');add((0,0,1),(1,0,0),'10.2')
    for c,d in product(range(2),repeat=2):
        J=inc(0)
        if J is None:add((1,m+15+c+2*d,0),(10,base(0)+c+2*d,gam(0)),'10.3')
        else:
            v=2**J;u=2**(J^1)
            add((1,m+15+c*v+d*u,0),(10,base(0)+d*u,gam(0)+c*v),'10.4')
        add((m+9,7+c+2*d,0),(1,m+15+c+2*d,0),'10.5')
    return rows

def audit_rows(m,rows):
    domain={};image={}; labels=Counter(); bad=[]
    for a,b,label in rows:
        labels[label]+=1
        if any(not 0<=v<=m+18 for v in a+b):bad.append(('range',a,b,label))
        if sum(a)!=sum(b):bad.append(('mass',a,b,label))
        if a in domain and domain[a]!=b:bad.append(('function',a,b,label))
        if b in image and image[b]!=a:bad.append(('injection',a,b,label))
        domain[a]=b;image[b]=a
    return bad,domain,labels

def complete(m,g,extra=()):
    """Complete within each mass fiber, lexically pairing unused domain/range."""
    out=dict(g)
    for a,b in extra:
        assert a not in out and b not in out.values() and sum(a)==sum(b)
        out[a]=b
    used=set(out.values()); ds=defaultdict(list); rs=defaultdict(list)
    for q in product(range(m+19),repeat=3):
        if q not in out:ds[sum(q)].append(q)
        if q not in used:rs[sum(q)].append(q)
    assert ds.keys()==rs.keys()
    for s in ds:
        assert len(ds[s])==len(rs[s])
        out.update(zip(ds[s],rs[s]))
    assert len(out)==(m+19)**3==len(set(out.values()))
    assert all(sum(a)==sum(b) for a,b in out.items())
    return out

def encode(m,delta,i,n0,n1):
    instruction,gam,inc=metadata(m,delta)
    a=defaultdict(lambda:[0,0,0])
    a[0]=[i+10,m+16-(i+10)-gam(i),gam(i)]
    for j,n in enumerate((n0,n1)):
        if n==0 and inc(i)==j:a[0][2]+=2**j
        else:a[n][1]+=2**j
    return {x:tuple(s) for x,s in a.items() if tuple(s)!=ZERO}

def mass(a):return sum(map(sum,a.values()))

def step(a,g):
    result={}
    for x in range(min(a,default=0)-1,max(a,default=0)+2):
        args=(a.get(x-1,ZERO)[2],a.get(x,ZERO)[1],a.get(x+1,ZERO)[0])
        if args not in g:raise KeyError((x,args))
        nxt=g[args]
        if nxt!=ZERO:result[x]=nxt
    return result

def machine_step(delta,i,n0,n1):
    n=[n0,n1]
    for I,j,op,k in delta:
        if i!=I:continue
        if op=='Z' and n[j]!=0 or op=='P' and n[j]==0 or op=='-' and n[j]==0:continue
        dt=2
        if op=='+':dt=2*n[j]+2;n[j]+=1
        if op=='-':dt=2*n[j];n[j]-=1
        return (k,*n),dt
    return None

def test_one_steps(m,delta,g,nmax=3):
    checks=0
    for i,n0,n1 in product(range(m),range(nmax+1),range(nmax+1)):
        a=encode(m,delta,i,n0,n1)
        assert mass(a)==m+19 and len(a)<=3
        target=machine_step(delta,i,n0,n1)
        if target is None:continue
        output,dt=target
        for t in range(dt):
            assert all(q[0]!=1 for q in a.values()),('premature halt',delta,i,n0,n1,t,a)
            a=step(a,g);assert mass(a)==m+19
        assert a==encode(m,delta,*output),(delta,(i,n0,n1),output,dt,a)
        checks+=1
    return checks

def source_options(m,i):
    opts=[()]
    for j in range(2):
        for op in '+-0':
            for k in range(1,m):opts.append(((i,j,op,k),))
        for a,b in product(range(m),repeat=2):
            q=[]
            if a:q.append((i,j,'Z',a))
            if b:q.append((i,j,'P',b))
            if q:opts.append(tuple(q))
    return opts

def random_delta(rng,m):
    delta=[]
    for i in rng.sample(list(range(m-1)),m-1):
        choices=source_options(m,i);rng.shuffle(choices)
        for add in choices:
            if valid(m,delta+list(add)):
                delta+=list(add);break
    return delta

def save_table(name,g):
    path=Path(__file__).with_name(name)
    with path.open('w') as f:
        writer=csv.writer(f);writer.writerow(['input_R','input_C','input_L','output_L','output_C','output_R'])
        for a,b in sorted(g.items()):writer.writerow(a+b)
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    report={}; coverage=Counter();count=checks=0
    for options in product(*(source_options(3,i) for i in range(2))):
        delta=sum((list(x) for x in options),[])
        if not valid(3,delta):continue
        rows=compile_partial(3,delta);bad,g,labels=audit_rows(3,rows)
        assert not bad,(delta,bad)
        coverage.update(labels);count+=1
        checks+=test_one_steps(3,delta,g)
    report['exhaustive_m3']={'machines':count,'legal_macrostep_checks_n0_n1_0_to_3':checks}
    rng=random.Random(20261002);count=checks=0
    for _ in range(3000):
        m=rng.randrange(2,13);delta=random_delta(rng,m)
        bad,g,labels=audit_rows(m,compile_partial(m,delta));assert not bad,(delta,bad)
        coverage.update(labels);count+=1
        if count<=300:checks+=test_one_steps(m,delta,g)
    report['random_m2_to_m12']={'machines':count,'first_300_macrostep_checks_n0_n1_0_to_3':checks}
    report['scheme_coverage']=dict(sorted(coverage.items()))
    # Both target increment types, no-op can be tagged with the other counter.
    printed=[]
    for j in range(2):
        delta=[(0,1-j,'0',1),(1,j,'+',2)]
        rows=compile_partial(3,delta,printed_82=True)
        bad,g,_=audit_rows(3,rows)
        printed.append({'target_increment_counter':j,'failures':bad})
    report['printed_82_counterexamples']=printed
    # Published doubling example; independent exact-time check to final signal.
    delta=[(0,1,'Z',1),(1,0,'Z',6),(1,0,'P',2),(2,0,'-',3),(3,1,'+',4),(4,1,'+',5),(5,1,'P',1)]
    _,partial,_=audit_rows(7,compile_partial(7,delta));g=complete(7,partial)
    report['completed_doubling_table']={'domain_size':len(g),'partial_rows':len(partial)}
    save_table('doubling-complete.csv',g)
    halt=[]
    for n in range(11):
        I=(0,n,0);a=encode(7,delta,*I);t=0;k=0
        while I[0]!=6:
            I2,dt=machine_step(delta,*I)
            for _ in range(dt):a=step(a,g);t+=1;assert mass(a)==26
            I=I2;k+=1;assert a==encode(7,delta,*I)
        assert I==(6,0,2*n)
        assert a.get(0,ZERO)[0]==16
        a=step(a,g);assert a.get(-1,ZERO)[2]==16
        a=step(a,g);assert a.get(0,ZERO)[0]==1
        for s in range(1,9):
            a=step(a,g);assert a.get(-s,ZERO)==(1,0,0)
            assert a.get(0,ZERO)[1]==25 if n==0 else a.get(0,ZERO)[1]==23
            if n:assert a[2*n]==(0,2,0)
            assert mass(a)==26
        halt.append({'input_n':n,'macrosteps':k,'time_qf':t,'time_L1_at_origin':t+2,'time_L1_at_minus1':t+3})
    report['doubling_halting_tests']=halt
    # Initial travelling-signal predecessor, including all initial op types.
    initial_checks=0
    for m in (2,3):
        for opt in source_options(m,0):
            delta=list(opt)
            _,g,_=audit_rows(m,compile_partial(m,delta))
            for n0,n1 in product(range(4),repeat=2):
                before=defaultdict(lambda:[0,0,0]);before[-1][2]=1;before[0][1]=m+15
                for j,n in enumerate((n0,n1)):before[n][1]+=2**j
                before={x:tuple(q) for x,q in before.items()}
                assert step(before,g)==encode(m,delta,0,n0,n1)
                initial_checks+=1
    report['initial_signal_predecessor_tests']=initial_checks
    # A legal reversible partial machine at a stuck decrement-zero ID can
    # encounter unlisted rules. A conserving injective completion can even
    # introduce the same left-channel signal used as a halt detector.
    delta=[(0,0,'-',1)];_,partial,_=audit_rows(2,compile_partial(2,delta))
    a=encode(2,delta,0,0,0);a=step(a,partial)
    try:step(a,partial)
    except KeyError as e:report['invalid_decrement_zero_undefined_at_t2']=e.args[0]
    else:raise AssertionError('Expected undefined rule')
    witness=((10,7,0),(1,16,0));g=complete(2,partial,[witness]);a=step(a,g)
    assert a[0][0]==1
    report['invalid_decrement_zero_false_signal_completion']={'extra_rule':witness,'state_t2':a,'mass':mass(a)}
    save_table('false-signal-complete.csv',g)
    a=encode(2,delta,0,0,0);trace=[]
    for t in range(9):
        trace.append({'time':t,'configuration':dict(sorted(a.items())),'mass':mass(a),'observer_L_minus1':a.get(-1,ZERO)[0]})
        if t==3:assert a.get(-1,ZERO)[0]==1
        a=step(a,g)
    report['false_signal_replay_t0_through_t8']=trace
    # Unconditional identity fill is not generally a permutation.
    assert any(b not in partial and b!=a for a,b in partial.items())
    a,b=next((a,b) for a,b in partial.items() if b not in partial and a!=b)
    report['identity_completion_collision']={'specified':(a,b),'identity_would_add':(b,b)}
    path=Path(__file__).with_name('audit-results.json');path.write_text(json.dumps(report,indent=2))
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
