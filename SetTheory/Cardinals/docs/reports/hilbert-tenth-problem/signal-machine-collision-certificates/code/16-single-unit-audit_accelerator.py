#!/usr/bin/env python3
"""Independent targeted audit; imports but does not edit the author's harness."""
import importlib.util, sys, json, hashlib, random, argparse
from itertools import product, permutations
from pathlib import Path
ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--module',type=Path,default=ROOT.parent/'test_single_unit_acceleration.py')
parser.add_argument('--output',type=Path,default=ROOT/'audit-results.json')
args=parser.parse_args()
SOURCE=args.module.resolve()
spec=importlib.util.spec_from_file_location('subject',SOURCE)
m=importlib.util.module_from_spec(spec);sys.modules[spec.name]=m;spec.loader.exec_module(m)
COUNTS={}
def count(k,n=1): COUNTS[k]=COUNTS.get(k,0)+n

def assert_mass(ca,c):
    # Use raw_step directly, independently of CA.step's assertion.
    out=ca.raw_step(c)
    assert sum(ca.weights[s] for s in c.values())==sum(ca.weights[s] for s in out.values()),(ca.name,c,out)
    assert all(s in ca.weights for s in out.values())
    count('finite_window_conservation_cases')

# Independent graph traversal constructs and checks all eight potential equations.
def potential(rule):
    adjacency={v:[] for v in product((0,1),repeat=2)}
    for a,b,c in product((0,1),repeat=3):
        d=((rule>>(4*a+2*b+c))&1)-b
        adjacency[(a,b)].append(((b,c),d))
        adjacency[(b,c)].append(((a,b),-d))
    values={(0,0):0}; todo=[(0,0)]
    while todo:
        u=todo.pop()
        for v,d in adjacency[u]:
            p=values[u]+d
            if v in values:
                if values[v]!=p:return None
            else:values[v]=p;todo.append(v)
    assert len(values)==4
    for a,b,c in product((0,1),repeat=3):
        assert ((rule>>(4*a+2*b+c))&1)-b == values[(b,c)]-values[(a,b)]
    return {''.join(map(str,k)):v for k,v in values.items()}
certs={r:potential(r) for r in range(256)}
certs={r:p for r,p in certs.items() if p is not None}
assert sorted(certs)==[170,184,204,226,240]
assert m.conservative_ecas()==sorted(certs)
COUNTS['independently_classified_elementary_rules']=256

cas=[m.right_ca(mask,d) for mask in range(8) for d in (-1,1)]+[m.eca_ca(r) for r in certs]+[m.integer_four_state_ca(),m.typed_ca()]
# Complete finite windows, not an exhaustive proof over infinite configurations.
for ca in cas:
    alphabet=[None]+list(ca.weights)
    width=11 if len(alphabet)==2 else (8 if len(alphabet)==4 else 5)
    for row in product(alphabet,repeat=width):
        c={i-width//2:s for i,s in enumerate(row) if s is not None}
        assert_mass(ca,c)

# Multi-center rewrites at exclusion boundary distances, with varied neighboring units.
for ca in [m.integer_four_state_ca(),m.typed_ca()]:
    heavy=[s for s,w in ca.weights.items() if w>=2]
    for d,a,b,bits in product(range(1,8),heavy,heavy,product((0,1),repeat=4)):
        c={0:a,d:b}
        for x,on in zip((-1,1,d-1,d+1),bits):
            if on and x not in c:c[x]='u'
        assert_mass(ca,c)
        translated={x-10**20:s for x,s in c.items()}
        assert ca.raw_step(translated)=={x-10**20:s for x,s in ca.raw_step(c).items()}
        count('rewrite_boundary_translation_cases')

# Check actual CA locality independently by cropping to the declared radius at outputs.
rng=random.Random(7013)
for ca in cas:
    for _ in range(100):
        c={x:rng.choice(list(ca.weights)) for x in range(-20,21) if rng.random()<.45}
        full=ca.raw_step(c)
        for x in (-8,-1,0,1,8):
            crop={y:s for y,s in c.items() if abs(y-x)<=ca.radius}
            assert ca.raw_step(crop).get(x)==full.get(x),(ca.name,x,c)
            count('finite_locality_checks')

# Long integer arithmetic checks have predetermined least hitting times.
for D in (-10**31-9,-7,-1,1,13,10**29+3):
    for A in (-10**60+4,0,10**61-21):
        for n in (0,1,10**35+11):
            target=A+n*D; w=(abs(D)-1)//3
            assert m.first_linear_hit(A,D,target-w,target+w)==n
            count('huge_linear_solver_cases')
for A in (-10**60,0,10**60):
    assert m.first_linear_hit(A,0,A,A)==0
    assert m.first_linear_hit(A,0,A+1,A+2) is None
    assert m.first_linear_hit(A,2,A+3,A+3) is None
    assert m.first_linear_hit(A,-2,A-3,A-3) is None
    count('huge_linear_solver_cases',4)

# Dense cases near S, 2S and 4S, both orientations, including insertion-order changes.
for ca in cas:
    S=ca.S; ds=sorted(set([1,S,max(1,S-1),S+1,2*S-1,2*S,2*S+1,4*S-1,4*S,4*S+1]))
    initial=[{}, {-3:'u'}]
    for d in ds:
        initial.append({0:'u',d:'u'})
        for total in (max(d+1,4*S-1),max(d+1,4*S),max(d+1,4*S+1),d+2*S-1,d+2*S,d+2*S+1):
            if total>d:initial.append({0:'u',d:'u',total:'u'})
    for s,w in ca.weights.items():
        if w==2:
            for b in ds:initial.extend([{0:s,b:'u'},{0:s,-b:'u'}])
        if w==3:initial.append({0:s})
    seen=set()
    for c in initial:
        key=tuple(sorted(c.items()))
        if key in seen:continue
        seen.add(key)
        # Reverse dictionary insertion and translate the whole input independently.
        c=dict(reversed(list(c.items())))
        acc=m.Accelerator(ca,c);cur=dict(c)
        off=-10**20+37
        translated=m.Accelerator(ca,{x+off:s for x,s in c.items()})
        for t in range(100):
            assert acc.at(t)==cur,(ca.name,c,t,acc.at(t),cur)
            assert translated.at(t)=={x+off:s for x,s in cur.items()},(ca.name,c,t,'translation')
            cur=ca.step(cur);count('boundary_direct_time_comparisons')
        count('boundary_orbit_cases')
    # Direct first-core checks for each connected pair shape and every nearby marker.
    shapes=[{0:'u',d:'u'} for d in range(1,2*S+1)]+[{0:s} for s,w in ca.weights.items() if w==2]
    for shape in shapes:
        p=m.profile(ca,shape)
        for b in range(-6*S-2,6*S+3):
            expected=None;cur=dict(shape)
            for t in range(200):
                if max(max(cur),b)-min(min(cur),b)<=4*S:
                    expected=t;break
                cur=ca.step(cur)
            got=m.first_core(p,b,4*S)
            assert got==expected,(ca.name,shape,b,got,expected)
            count('first_core_direct_comparisons')

# Huge gaps: closed-form independent expectations, not mere mass checks.
G=10**40+17; HUGE=10**80+123
for direction in (-1,1):
    ca=m.right_ca(7,direction)
    initial={0:'u',direction:'u',direction*G:'u'}
    acc=m.Accelerator(ca,initial)
    hit=2*(G-4*ca.S)
    for t in [0,1,2,10**30,hit-2,hit-1,hit]:
        n,r=divmod(t,2)
        expected={direction*n:'u',direction*(n+1+r):'u',direction*G:'u'}
        assert acc.at(t)==expected,(direction,t,acc.at(t),expected)
        count('huge_gap_closed_form_comparisons')
    # Re-anchor at exact entry and compare direct dynamics for both orientations.
    cur=acc.at(hit)
    for extra in range(150):
        assert acc.at(hit+extra)==cur
        cur=ca.step(cur);count('huge_gap_postentry_direct_comparisons')
    # Reflection equivariance of left/right families also at enormous postentry times.
    other=m.Accelerator(m.right_ca(7,-direction),{-x:s for x,s in initial.items()})
    assert other.at(HUGE)=={-x:s for x,s in acc.at(HUGE).items()}
    count('huge_time_reflection_comparisons')

ca=m.integer_four_state_ca();acc=m.Accelerator(ca,{0:'2',G:'u'})
for t in [0,1,G-21,G-20,G-1,G,G+1,G+2,HUGE]:
    if t<G:expected={t:'2',G:'u'}
    elif t==G:expected={G-1:'3'}
    else:expected={G-2:'u',t-1:'2'}
    assert acc.at(t)==expected,(t,acc.at(t),expected)
    count('huge_gap_closed_form_comparisons')
ca=m.typed_ca()
for label,sign in [('A',1),('L',-1)]:
    acc=m.Accelerator(ca,{0:label,sign*G:'u'})
    center=sign*G-sign
    for t in [0,1,G-21,G-20,G-1,G,G+1,G+2,G+3,HUGE]:
        if t<G:expected={sign*t:label,sign*G:'u'}
        else:
            r=(t-G)%3
            expected=({center:'H'} if r==0 else {center-1:'u',center+(1 if r==1 else 0):'L'})
        assert acc.at(t)==expected,(label,t,acc.at(t),expected)
        count('huge_gap_closed_form_comparisons')
# Zero-drift phase walker, transient splitting into stationary units, and positive escape.
for label in ('P','D','K'):
    acc=m.Accelerator(ca,{0:label,G:'u'} if label!='K' else {0:'K'})
    for t in [0,1,2,3,HUGE,HUGE+1]:
        if label=='P': expected=({0:'P',G:'u'} if t%2==0 else {1:'Q',G:'u'})
        elif label=='D':expected=({0:'D',G:'u'} if t==0 else ({0:'C',G:'u'} if t==1 else {-1:'u',1:'u',G:'u'}))
        else:expected=({0:'K'} if t==0 else {-1:'u',t:'A'})
        assert acc.at(t)==expected,(label,t,acc.at(t),expected)
        count('huge_gap_closed_form_comparisons')

# The revised ECA evaluator is sparse: verify huge gaps directly as well.
for rule in certs:
    ca=m.eca_ca(rule)
    for initial in ({-G:'u',0:'u',G:'u'},{0:'u',1:'u',G:'u'},{-G:'u',0:'u',1:'u'}):
        acc=m.Accelerator(ca,initial);cur=dict(initial)
        for t in range(60):
            assert acc.at(t)==cur,(rule,initial,t)
            cur=ca.step(cur);count('sparse_eca_huge_gap_direct_comparisons')
    independent={-G:'u',0:'u',G:'u'}
    assert ca.step(independent)==independent
    assert m.Accelerator(ca,independent).at(HUGE)==independent
    count('sparse_eca_huge_time_fixed_checks')

COUNTS.update(status='PASS',rules_tested=len(cas),source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),eca_potentials=certs)
args.output.write_text(json.dumps(COUNTS,indent=2)+'\n')
print(json.dumps(COUNTS,indent=2))
