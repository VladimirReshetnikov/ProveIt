"""Exact signal-stack replay and homogeneous integer event-lift checks.

Primary gadget: Durand-Lose, AGC 6 (2012), sections 3--4.
The literal universal six-symbol instantiation is in instantiate_morita.py.
"""
from fractions import Fraction as F
from math import lcm
from itertools import product
import json


def stack_machine(l=2):
    # c=3(l+2) clears every speed denominator in the general gadget.
    c=3*(l+2)
    speed={f'mark{i}':F(0) for i in range(l+1)}
    speed.update(mem=F(0), ml=F(-c), mr=F(c), catch=F(c,3),
                 fix=F(-c*l,l+2), ack=F(c), gl=F(-c),
                 gr=F(c*l,l+2), set=F(-c,3))
    for v in range(1,l+1):
        speed.update({f'sl{v}':F(-c), f'sr{v}':F(c),
                      f'vl{v}':F(-c), f'vr{v}':F(c)})
    rules={}
    def add(a,b):
        a,b=frozenset(a),frozenset(b)
        assert len(a)==len(b)==2
        assert len({speed[x] for x in a})==2
        assert len({speed[x] for x in b})==2
        assert a not in rules or rules[a]==b
        rules[a]=b
    add(('mark0','ml'),('mark0','mr'))
    add(('mr','catch'),('ml','fix'))
    add(('mr','fix'),('mem','ack'))
    add(('mem','gl'),('ml','gr'))
    add(('mr','gr'),('ml','set'))
    for v in range(1,l+1):
        add(('mem',f'sl{v}'),('ml',f'sr{v}'))
        add((f'sr{v}',f'mark{v}'),(f'mark{v}','catch'))
        add((f'mark{v}','set'),(f'vl{v}',f'mark{v}'))
        add(('mr',f'vl{v}'),('mem',f'vr{v}'))
        for i in range(1,l+1):
            for label in (f'sl{v}',f'vr{v}'):
                add((label,f'mark{i}'),(label,f'mark{i}'))
            if i<v:
                for label in (f'sr{v}',f'vl{v}'):
                    add((label,f'mark{i}'),(label,f'mark{i}'))
    for i in range(1,l+1):
        for label in ('ml','mr','fix','ack','gl','gr'):
            add((label,f'mark{i}'),(label,f'mark{i}'))
    assert len(set(rules.values()))==len(rules), 'Global local-rule injectivity'
    # Divide common speed gcd so the binary case has speeds 0,+/-2,+/-3,+/-6.
    from math import gcd
    d=0
    for v in speed.values():
        assert v.denominator==1
        d=gcd(d,abs(v.numerator))
    speed={a:v/d for a,v in speed.items()}
    return speed,rules


def event(conf,speed,rules,check_lift=True):
    """One complete simultaneous collision batch from a post-event germ.

    conf is ordered [(position,label)]. Equal-coordinate runs must have
    strictly increasing velocities. Undefined collisions raise ValueError.
    Return updated germ, duration, and exact branch map/guard receipt.
    """
    n=len(conf)
    g=[conf[i+1][0]-conf[i][0] for i in range(n-1)]
    v=[speed[a] for _,a in conf]
    c=[v[i]-v[i+1] for i in range(n-1)]
    assert all(x>=0 for x in g)
    assert all(g[i]>0 or c[i]<0 for i in range(n-1)), 'Invalid post-event germ'
    closing=[i for i in range(n-1) if c[i]>0]
    if not closing:
        return None
    dt=min(g[i]/c[i] for i in closing)
    assert dt>0
    J={i for i in closing if g[i]==c[i]*dt}
    j=min(J)
    guard=[c[j]*g[i]-c[i]*g[j] for i in range(n-1)]
    assert all(guard[i]==0 if i in J else guard[i]>0 for i in range(n-1))
    end=[x+speed[a]*dt for x,a in conf]
    assert all(end[i]<=end[i+1] for i in range(n-1))
    groups=[]
    start=0
    for i in range(n):
        if i==n-1 or i not in J:
            groups.append((start,i+1))
            start=i+1
    result=[]
    row_indices=[]
    for gi,(a,b) in enumerate(groups):
        if gi:
            # New inter-group gap is the old boundary endpoint gap.
            row_indices.append(a-1)
        labels=[conf[k][1] for k in range(a,b)]
        if b-a>1:
            key=frozenset(labels)
            if key not in rules:
                raise ValueError(('undefined collision',labels,end[a]))
            labels=sorted(rules[key],key=speed.__getitem__)
        assert labels
        for k,label in enumerate(labels):
            if k:
                row_indices.append(None)
            result.append((end[a],label))
    assert len(row_indices)==len(result)-1
    # A = E (I - c e_j^T/c_j). E includes rows of zero for freshly
    # emitted co-located particles; it keeps old inter-block boundaries.
    A=[]
    for ix in row_indices:
        row=[F(0)]*(n-1)
        if ix is not None:
            row[ix]=F(1)
            row[j]-=c[ix]/c[j]
        A.append(row)
    newg=[result[i+1][0]-result[i][0] for i in range(len(result)-1)]
    assert newg==[sum(a*x for a,x in zip(row,g) if a) for row in A]
    # Every rule here preserves its own cardinality. Replacement therefore
    # leaves the ordered endpoint-position multiset, and hence all gaps,
    # unchanged. Use the stronger scaled-projection matrix, even for ties.
    assert len(result)==n
    A=[]
    for ix in range(n-1):
        row=[F(int(k==ix)) for k in range(n-1)]
        row[j]-=c[ix]/c[j]
        A.append(row)
    assert newg==[sum(a*x for a,x in zip(row,g) if a) for row in A]
    velocities=set(speed.values())
    D=lcm(*(int(abs(a-b)) for a in velocities for b in velocities if a!=b))
    M=[[D*a for a in row] for row in A]
    assert all(x.denominator==1 for row in M for x in row)
    assert all(x==0 for x in M[j])
    assert sum(x!=0 for row in M for x in row)<=2*(n-2)
    if set(speed.values())<={F(x) for x in (-6,-3,-2,0,2,3,6)}:
        assert all(abs(x)<=4320 for row in M for x in row)
    if check_lift:
        Q=lcm(*(x.denominator for x in g))
        h=[Q*x for x in g]
        newh=[Q*D*x for x in newg]
        assert newh==[sum(a*x for a,x in zip(row,h) if a) for row in M]
        assert all(x.denominator==1 and x>=0 for x in newh)
    return result,dt,dict(J=sorted(J),pivot=j,A=A,D=D,guards=guard,
                         closing=[int(x) for x in c],pivot_speed=int(c[j]))


def adaptive_lift(h,scale,receipt,new_conf,span=None):
    """Whole-orbit integer lift using the canonical pivot speed each step.

    h=scale*g with an initial common denominator scale=Q. No gcd reduction
    or existential scale variable is used. scale is retained only by this
    test oracle; fixed-span compiled orbits recover it from sum(h)/span.
    """
    j=receipt['pivot']; c=receipt['closing']; cj=receipt['pivot_speed']
    assert cj>0 and cj==c[j]
    oldspan=sum(h)
    newh=[cj*x-ci*h[j] for x,ci in zip(h,c)]
    newscale=scale*cj
    assert all(isinstance(x,int) and x>=0 for x in newh)
    assert {i for i,x in enumerate(newh) if x==0}==set(receipt['J'])
    gaps=[new_conf[i+1][0]-new_conf[i][0] for i in range(len(new_conf)-1)]
    assert all(x*g.denominator==newscale*g.numerator for x,g in zip(newh,gaps))
    assert sum(newh)==cj*oldspan-sum(c)*h[j]
    if span is not None:
        assert sum(newh)==cj*oldspan==span*newscale
        assert all(span*x*g.denominator==sum(newh)*g.numerator for x,g in zip(newh,gaps))
    return newh,newscale


def blank_stack(word,l):
    s=F(1,l)
    for v in reversed(word):
        assert 1<=v<=l
        s=(v+s)/(l+1)
    return s


def run_stack(s,l,operation,value=None):
    speed,rules=stack_machine(l)
    token=f'sl{value}' if operation=='push' else 'gl'
    conf=[(F(i),f'mark{i}') for i in range(l+1)]+[(s,'mem'),(F(l+1),token)]
    conf.sort()
    gaps=[conf[i+1][0]-conf[i][0] for i in range(len(conf)-1)]
    scale=lcm(*(g.denominator for g in gaps)); h=[int(scale*g) for g in gaps]
    count=0
    simultaneous=0
    total=F(0)
    # Each primitive has a bounded number of crossings of finitely many marks.
    for _ in range(1000):
        out=event(conf,speed,rules)
        if out is None:
            break
        conf,dt,rec=out
        h,scale=adaptive_lift(h,scale,rec,conf)
        count+=len(rec['J'])
        simultaneous+=len(rec['J'])>1
        total+=dt
        assert len(conf)==l+3
    else:
        raise AssertionError('Unexpected nontermination of finite stack operation')
    mem=[x for x,a in conf if a=='mem']
    assert len(mem)==1
    controls=[a for x,a in conf if not a.startswith('mark') and a!='mem']
    assert len(controls)==1
    if operation=='push':
        assert mem[0]==(value+s)/(l+1)
        assert controls==['ack']
    else:
        v=(l+1)*s
        top=v.numerator//v.denominator
        assert 1<=top<=l
        assert mem[0]==v-top
        assert controls==[f'vr{top}']
    return mem[0],controls[0],count,simultaneous,total


def compile_tm(write,move,initial,halting,l=2,halt_pairs=None,initial_side='R'):
    """Compile an alternating reversible write/move TM, plus finite halt exits.

    write[(q,a)]=(r,b); move[r]=(next_q,'L' or 'R').
    initial_side selects the initial read stack and must agree with an
    existing incoming move, if any. This is an executable
    compiler, not an explicit universal source program.
    """
    base,brules=stack_machine(l)
    assert len(set(write.values()))==len(write)
    assert len({q for q,d in move.values()})==len(move)
    assert all(d in ('L','R') for q,d in move.values())
    incoming={q:d for q,d in move.values()}
    assert initial_side in ('L','R')
    assert initial not in incoming or incoming[initial]==initial_side
    incoming[initial]=initial_side
    if halt_pairs is None:
        halt_pairs={(q,a) for q in halting for a in range(1,l+1)}
    assert {r for r,b in write.values()}<=set(move)
    assert {q for q,a in write}|{q for q,a in halt_pairs}<=set(incoming)
    assert ({q for q,a in write}|{q for q,a in halt_pairs}|set(incoming)).isdisjoint(move)
    assert all(1<=a<=l and 1<=b<=l for (q,a),(r,b) in write.items())
    assert all(1<=a<=l and (q,a) not in write for q,a in halt_pairs)
    speed={}
    rules={}
    for side,sign in (('L',1),('R',-1)):
        speed.update({side+':'+a:sign*v for a,v in base.items()})
        for a,b in brules.items():
            rules[frozenset(side+':'+x for x in a)]=frozenset(side+':'+x for x in b)
    states={initial}|set(halting)|{q for q,a in write}|{r for r,b in write.values()}|set(move)
    states|={q for q,d in move.values()}
    states|={q for q,a in halt_pairs}
    speed.update({'q:'+q:F(0) for q in states})
    def add(a,b):
        key=frozenset(a)
        assert key not in rules
        rules[key]=frozenset(b)
    for (q,a),(r,b) in write.items():
        target,direction=move[r]
        store='L' if direction=='R' else 'R'
        add(('q:'+q,incoming[q]+':vr'+str(a)),('q:'+r,store+':sl'+str(b)))
    for r,(q,direction) in move.items():
        store='L' if direction=='R' else 'R'
        add(('q:'+r,store+':ack'),('q:'+q,direction+':gl'))
    statics=[a for a,v in speed.items() if v==0 and not a.startswith('q:')]
    c=max(speed.values())
    for q,a in sorted(halt_pairs):
        h,e=f'h:{q}:{a}',f'e:{q}:{a}'
        speed[h]=F(0); speed[e]=c
        add(('q:'+q,incoming[q]+':vr'+str(a)),(h,e))
        for s in statics:
            add((e,s),(e,s))
    assert len(set(rules.values()))==len(rules), 'Compiled rule table not injective'
    for a,b in rules.items():
        assert len(a)==len(b)==2
        assert len({speed[x] for x in a})==2
        assert len({speed[x] for x in b})==2
    return speed,rules


def sample_tm_replay(word,left_word=()):
    # Copy first symbol, complement second symbol, then halt at third symbol.
    write={('start',a):('move1',a) for a in (1,2)}
    write.update({('second',a):('move2',3-a) for a in (1,2)})
    move={'move1':('second','R'),'move2':('halt','R')}
    speed,rules=compile_tm(write,move,'start',{'halt'})
    conf=[(F(-4+i),'L:mark'+str(i)) for i in range(3)]
    conf += [(F(4-i),'R:mark'+str(i)) for i in range(3)]
    conf += [(-4+blank_stack(left_word,2),'L:mem'),(4-blank_stack(word,2),'R:mem'),
             (F(0),'q:start'),(F(1),'R:gl')]
    conf.sort()
    gaps=[conf[i+1][0]-conf[i][0] for i in range(9)]
    scale=lcm(*(g.denominator for g in gaps)); h=[int(scale*g) for g in gaps]
    steps=0
    for _ in range(1000):
        out=event(conf,speed,rules)
        if out is None:
            break
        conf,dt,rec=out
        h,scale=adaptive_lift(h,scale,rec,conf,span=8)
        assert len(conf)==10
        steps+=1
        # Until halt, outermost markers enclose everything and give span8.
        if not any(a.startswith('h:') for x,a in conf):
            assert conf[-1][0]-conf[0][0]==8
    else:
        raise AssertionError('Sample TM failed to halt')
    w=list(word)+[1,1,1]
    values={a:x for x,a in conf}
    assert values['L:mem']==-4+blank_stack((3-w[1],w[0])+tuple(left_word),2)
    assert values['R:mem']==4-blank_stack(word[3:],2)
    assert values[f'h:halt:{w[2]}']==0
    assert any(a.startswith('e:') for x,a in conf)
    return steps


def left_entry_replay():
    write={('start',a):('move',a) for a in (1,2)}
    move={'move':('halt','L')}
    speed,rules=compile_tm(write,move,'start',{'halt'},initial_side='L')
    conf=[(F(-4+i),'L:mark'+str(i)) for i in range(3)]
    conf += [(F(4-i),'R:mark'+str(i)) for i in range(3)]
    conf += [(-4+blank_stack((2,1,2),2),'L:mem'),
             (4-blank_stack((2,2),2),'R:mem'),
             (F(0),'q:start'),(F(-1),'L:gl')]
    conf.sort(); steps=0
    gaps=[conf[i+1][0]-conf[i][0] for i in range(9)]
    scale=lcm(*(g.denominator for g in gaps)); h=[int(scale*g) for g in gaps]
    for _ in range(1000):
        out=event(conf,speed,rules)
        if out is None:
            break
        conf,dt,rec=out; steps+=1
        h,scale=adaptive_lift(h,scale,rec,conf,span=8)
        assert len(conf)==10
    else:
        raise AssertionError('Left-entry replay failed to terminate')
    values={a:x for x,a in conf}
    assert values['L:mem']==-4+blank_stack((2,),2)
    assert values['R:mem']==4-blank_stack((2,2,2),2)
    assert values['h:halt:1']==0
    return steps


def main():
    cases=events=ties=0
    for l in (2,3,4):
        for length in range(4):
            for word in product(range(1,l+1),repeat=length):
                s=blank_stack(word,l)
                assert F(1,l)<=s<1
                for v in range(1,l+1):
                    new,_,cnt,sim,t=run_stack(s,l,'push',v)
                    cases+=1; events+=cnt; ties+=sim
                    old,top,cnt,sim,t=run_stack(new,l,'pop')
                    cases+=1; events+=cnt; ties+=sim
                    assert old==s and top==f'vr{v}'
                _,_,cnt,sim,t=run_stack(s,l,'pop')
                cases+=1; events+=cnt; ties+=sim
    speed,rules=stack_machine(2)
    D=lcm(*(int(abs(a-b)) for a in speed.values() for b in speed.values() if a!=b))
    tm_cases=tm_batches=0
    for length in range(6):
        for word in product((1,2),repeat=length):
            tm_batches+=sample_tm_replay(word)
            tm_cases+=1
    two_half_batches=sample_tm_replay((2,1,2),(2,1,2))
    left_entry_batches=left_entry_replay()
    # Exhaustive check of the nonnegative quadratic branch-copy device.
    # Branch0: x=0 -> y=0; branch1: x>0 -> y=2x.
    packet_checks=packet_zeros=0
    for x in range(4):
        for y in range(8):
            zeros=[]
            for b0,b1,z0,z1,s in product(range(5),repeat=5):
                p=((b0+b1-1)**2+(x-z0-z1)**2+(y-2*z1)**2
                   +z0*z0+(z1-b1-s)**2+b1*z0+b0*z1)
                assert p>=0
                packet_checks+=1
                if p==0:
                    zeros.append((b0,b1,z0,z1,s))
            assert len(zeros)==int(y==2*x)
            packet_zeros+=len(zeros)
    print(json.dumps(dict(status='PASS',stack_operations=cases,
                         binary_collisions=events,simultaneous_batches=ties,
                         binary_speeds=sorted({int(x) for x in speed.values()}),
                         binary_D=D,binary_module_rules=len(rules),
                         compiled_tm_cases=tm_cases,compiled_tm_batches=tm_batches,
                         additional_two_half_batches=two_half_batches,
                         left_entry_batches=left_entry_batches,
                         quadratic_packet_assignments=packet_checks,
                         quadratic_packet_canonical_zeros=packet_zeros,
                         adaptive_pivot_lift_checked_on_all_runs=True,
                         optional_uniform_D_lift_checked_per_event=True,
                         full_machine_population_formula='2*l+6',
                         limitation='No binary universal table in this script; literal six-symbol table is in instantiate_morita.py'),indent=2))


if __name__=='__main__':
    main()
