#!/usr/bin/env python3
"""Independent finite regression of the mathematical proof, standard library only.
No imports from the producer's implementation. This is not formal verification.
"""
import hashlib, itertools, json, random
from pathlib import Path

ROOT=Path(__file__).resolve().parent
COUNTS={}
COVERAGE={}
def add(k,n=1): COUNTS[k]=COUNTS.get(k,0)+n
def cover(k,n=1): COVERAGE[k]=COVERAGE.get(k,0)+n

def control(alpha,disp,a,b):
    seen={}; phases=[]; l=r=0
    while (a,b) not in seen:
        seen[(a,b)]=len(phases); phases.append((a,b,l,r))
        l+=disp[a]; r+=disp[b]; a,b=alpha[a],alpha[b]
    mu=seen[(a,b)]; p=len(phases)-mu
    dl=l-phases[mu][2]; dr=r-phases[mu][3]
    return mu,p,dl,dr,phases

def phase_at(C,T):
    mu,p,dl,dr,ph=C
    if T<mu: return ph[T]
    n,s=divmod(T-mu,p); a,b,l,r=ph[mu+s]
    return a,b,l+dl*n,r+dr*n

def safe_formula(C,g,H,T):
    mu,p,dl,dr,ph=C; D=dr-dl
    if T<mu:
        return all(g+ph[h][3]-ph[h][2]>H for h in range(T))
    k,s=divmod(T-mu,p)
    if any(g+ph[h][3]-ph[h][2]<=H for h in range(mu)): return False
    for j in range(p):
        top=k if j<s else k-1
        if top<0: continue
        arg=top if D<0 else 0
        if g+ph[mu+j][3]-ph[mu+j][2]+D*arg<=H: return False
    return True

def guard_tests():
    # All finite singleton maps and permitted displacements for one/two types.
    for size in (1,2):
      for alpha in itertools.product(range(size),repeat=size):
       for radius in range(3):
        for disp in itertools.product(range(-radius,radius+1),repeat=size):
         for a,b in itertools.product(range(size),repeat=2):
          C=control(alpha,disp,a,b)
          for gap in range(2*radius+1,2*radius+13):
           A,B=a,b; L=R=0; raw_safe=True
           for T in range(41):
            assert safe_formula(C,gap,2*radius,T)==raw_safe
            assert phase_at(C,T)==(A,B,L,R)
            add('exhaustive_prefix_and_phase_cases')
            raw_safe &= gap+R-L>2*radius
            L+=disp[A];R+=disp[B];A,B=alpha[A],alpha[B]
    rng=random.Random(2026100201)
    for _ in range(2000):
        size=rng.randrange(3,9);radius=rng.randrange(1,6)
        alpha=[rng.randrange(size) for _ in range(size)]
        disp=[rng.randrange(-radius,radius+1) for _ in range(size)]
        a,b=rng.randrange(size),rng.randrange(size)
        C=control(alpha,disp,a,b);gap=rng.randrange(2*radius+1,200)
        A,B=a,b; L=R=0; raw_safe=True
        for T in range(81):
            assert safe_formula(C,gap,2*radius,T)==raw_safe
            assert phase_at(C,T)==(A,B,L,R)
            add('random_prefix_and_phase_cases')
            raw_safe &= gap+R-L>2*radius
            L+=disp[A];R+=disp[B];A,B=alpha[A],alpha[B]

# Three-channel collision/transport CAs. A state is a subset of three channels.
# Every local collision map preserves popcount, then channel i travels i-1.
# This is a total finite-alphabet radius-one conservative CA, even when collision
# is noninjective. It exercises splitting, merging, transients and free flights.
SPEED=(-1,0,1)
def ca_step(x,rule):
    out={}
    for pos,st in x.items():
        value=rule[st]
        for bit in range(3):
            if value & (1<<bit):
                p=pos+SPEED[bit]
                assert not (out.get(p,0)&(1<<bit))
                out[p]=out.get(p,0)|(1<<bit)
    return out

def norm(x):
    base=min(x)
    return tuple((p-base,s) for p,s in sorted(x.items())),base

def singleton_control(rule,a,b):
    alpha=[];disp=[]
    for bit in range(3):
        j=rule[1<<bit].bit_length()-1
        alpha.append(j);disp.append(SPEED[j])
    return control(alpha,disp,a.bit_length()-1,b.bit_length()-1)

def future_return(x,rule):
    (u,a),(v,b)=sorted(x.items()); C=singleton_control(rule,a,b)
    mu,p,dl,dr,ph=C; gap=v-u; D=dr-dl
    for _,_,l,r in ph:
        if gap+r-l<=2: return True
    return D<0

def orbit_templates(E,rule):
    # Each tuple is theta, period (0 for singleton time), states, positions, drift.
    templates=[]; seen_near={}; t=0; x=dict(E)
    while True:
        N,base=norm(x); near=(N[-1][0]<=2)
        if near and N in seen_near:
            cover('near_recurrent_templates')
            start,oldbase=seen_near[N];period=t-start;drift=base-oldbase
            out=[]
            for theta,_,states,positions,_ in templates:
                out.append((theta,period if theta>=start else 0,states,positions,
                            (drift,)*len(states) if theta>=start else (0,)*len(states)))
            return out
        if near: seen_near[N]=(t,base)
        elif not future_return(x,rule):
            cover('terminal_free_templates')
            (u,a),(v,b)=sorted(x.items()); C=singleton_control(rule,a,b)
            mu,p,dl,dr,ph=C
            for i,(a,b,l,r) in enumerate(ph):
                templates.append((t+i,0 if i<mu else p,(1<<a,1<<b),(u+l,v+r),
                                  (0,0) if i<mu else (dl,dr)))
            return templates
        states=tuple(s for p,s in sorted(x.items()));positions=tuple(sorted(x))
        templates.append((t,0,states,positions,(0,)*len(states)))
        x=ca_step(x,rule);t+=1
        assert t<10000

def at_templates(templates,T,offset):
    outputs=set()
    for theta,period,states,positions,drift in templates:
        if T<theta: continue
        if not period:
            if T!=theta: continue
            n=0
        else:
            n,rem=divmod(T-theta,period)
            if rem: continue
        output=tuple((offset+pos+n*d,s) for pos,d,s in zip(positions,drift,states))
        assert tuple(sorted(output))==output
        assert len({p for p,s in output})==len(output)
        outputs.add(output)
    return outputs

def ca_template_tests():
    rng=random.Random(2026100202)
    shapes=[((0,s),) for s in (3,5,6)]
    shapes += [((0,a),(g,b)) for g in (1,2) for a,b in itertools.product((1,2,4),repeat=2)]
    for ruleindex in range(20):
        layers={m:[s for s in range(8) if s.bit_count()==m] for m in range(4)}
        if ruleindex<10:
            rule=list(range(8))
            for states in layers.values():
                mapped=states.copy();rng.shuffle(mapped)
                for st,target in zip(states,mapped):rule[st]=target
        else:
            rule=[rng.choice(layers[s.bit_count()]) for s in range(8)]
        cover('noninjective_collision_rules' if len(set(rule))<8 else 'bijective_collision_rules')
        templates={E:orbit_templates(E,rule) for E in shapes}
        initials=[((0,s),) for s in (3,5,6)]
        initials += [((0,a),(g,b)) for g in range(1,15) for a,b in itertools.product((1,2,4),repeat=2)]
        for base in (-31,0,19):
          for initial in initials:
            x={p+base:s for p,s in initial}; raw=x.copy();E,offset=norm(x)
            entry=None
            if E[-1][0]<=2: entry=(0,E,offset)
            else:
                (u,a),(v,b)=sorted(x.items());C=singleton_control(rule,a,b);g=v-u
                for tau in range(51):
                    if safe_formula(C,g,2,tau):
                        aa,bb,l,r=phase_at(C,tau);egap=g+r-l
                        if 1<=egap<=2:
                            entry=(tau,((0,1<<aa),(egap,1<<bb)),u+l);break
            for T in range(51):
                predicted=set()
                if E[-1][0]>2 and safe_formula(C,g,2,T):
                    aa,bb,l,r=phase_at(C,T)
                    predicted.add(((u+l,1<<aa),(v+r,1<<bb)))
                if entry and T>=entry[0]:
                    tau,entryshape,xi=entry
                    predicted |= at_templates(templates[entryshape],T-tau,xi)
                assert predicted=={tuple(sorted(raw.items()))},(ruleindex,x,T,predicted,raw)
                add('timed_full_ca_configuration_cases')
                nxt=ca_step(raw,rule)
                if len(nxt)>len(raw):cover('splitting_steps')
                if len(nxt)<len(raw):cover('merging_steps')
                raw=nxt


def inequality_res(L,b,s): return b*(b-1),L-(2*b-1)*s-b+1

def congruence_res(L,d,qp,qm,a,h,b,s):
    return qp*qm,L-d*(qp-qm)-a,a+h-(d-1),b*(b-1),a-(2*b-1)*s-b

def canonical_inequality(L): return (1,L) if L>=0 else (0,-L-1)

def canonical_congruence(L,d):
    q,a=divmod(L,d)
    return max(q,0),max(-q,0),a,d-1-a,int(a>0),max(a-1,0)

def compiler_tests():
    for L in range(-30,31):
        sols=[(b,s) for b in range(5) for s in range(33) if not any(inequality_res(L,b,s))]
        assert sols==[canonical_inequality(L)]
        add('inequality_bounded_full_fiber_cases')
    for L in range(-20,21):
      for d in range(1,9):
        sols=[]
        # Exhaustively enumerate the displayed candidate box, with early rejection
        # by the first three residuals. These bounds contain the canonical tuple.
        for qp,qm in itertools.product(range(22),repeat=2):
            if qp*qm: continue
            for a in range(d+2):
                if L-d*(qp-qm)-a: continue
                for h in range(d+2):
                    if a+h-(d-1): continue
                    for b,s in itertools.product(range(5),range(d+2)):
                        W=(qp,qm,a,h,b,s)
                        if not any(congruence_res(L,d,*W)):sols.append(W)
        assert sols==[canonical_congruence(L,d)],(L,d,sols)
        add('congruence_bounded_full_fiber_cases')
    for L in (0,1,-1,10**300,-10**300,10**300+137,-10**300-137):
      for d in (1,2,7,10**150+31):
        W=canonical_congruence(L,d)
        assert not any(congruence_res(L,d,*W))
        assert (1-W[4])==int(L%d==0)
        for j in range(6):
            for delta in (-1,1):
                altered=list(W);altered[j]+=delta
                if altered[j]>=0:
                    assert any(congruence_res(L,d,*altered))
        add('large_signed_congruence_cases')
    for u,v in itertools.product((0,1),repeat=2):
      for gate,expected in (('and',u*v),('or',int(u or v)),('not',1-u)):
        good=[]
        for z in range(5):
            residual={'and':z-u*v,'or':z-u-v+u*v,'not':z-1+u}[gate]
            if residual==0:good.append(z)
        assert good==[expected]
        add('boolean_gate_bounded_full_fiber_cases')
    # Unconditionally evaluated repeated atoms in OR(A,NOT(A)) have one tuple.
    # The final output condition rejects false circuits, without dormant witnesses.
    for L in range(-15,16):
        b,s=canonical_inequality(L);b2,s2=canonical_inequality(L)
        neg=1-b2;out=b+neg-b*neg
        W=(b,s,b2,s2,neg,out)
        residuals=(*inequality_res(L,b,s),*inequality_res(L,b2,s2),neg-1+b2,out-b-neg+b*neg,out-1)
        assert not any(residuals) and len(W)==2*2+0*6+2 and len(residuals)==2*2+0*5+2+1
        add('repeated_atom_circuit_count_cases')
    # Constants: N^0 contains one empty tuple. True has P=0, false has P=1.
    assert sum([0**2])==0 and sum([(-1)**2])==1
    add('zero_witness_constant_cases',2)

if __name__=='__main__':
    guard_tests();ca_template_tests();compiler_tests()
    receipt={'status':'PASS','counts':COUNTS,'total':sum(COUNTS.values()),
             'ca_test_coverage':COVERAGE,
             'scope':'Independent finite arithmetic and actual conservative-CA component checks; not a formal proof, arbitrary-rule compiler, or quantifier-elimination implementation.',
             'seeds':[2026100201,2026100202],
             'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (ROOT/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
