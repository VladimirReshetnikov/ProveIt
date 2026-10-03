#!/usr/bin/env python3
"""Small executable tests for the unique-unit mass-three proof.
Not a formal verification or an exhaustive search over CA rules.
Python 3 standard library only. Run from any directory.
"""
from dataclasses import dataclass
from itertools import combinations, product
import json, random
from pathlib import Path


def norm(c):
    if not c: return (), 0
    a=min(c)
    return tuple(sorted((x-a,s) for x,s in c.items())),a

def shift(c,a): return {x+a:s for x,s in c.items()}
def span(c): return max(c)-min(c) if c else 0

@dataclass
class CA:
    name: str
    radius: int
    weights: dict
    raw_step: object
    delta: int = 0
    @property
    def S(self): return max(1,self.radius+abs(self.delta))
    def step(self,c):
        d=shift(self.raw_step(c),-self.delta)
        assert sum(self.weights[s] for s in c.values()) == sum(self.weights[s] for s in d.values())
        return d

def right_ca(mask,direction=1):
    # Each selected 10 pair swaps simultaneously; these pairs are disjoint.
    # h(left,right2)=0 at (0,0), so isolated units are fixed.
    def raw(c):
        b=set(c); moving=[]
        for x in b:
            if x+direction in b: continue
            context=(int(x-direction in b)<<1)|int(x+2*direction in b)
            if context and ((mask>>(context-1))&1): moving.append(x)
        out=b-set(moving)
        out.update(x+direction for x in moving)
        return {x:'u' for x in out}
    return CA(f'binary_{direction:+d}_{mask}',2,{'u':1},raw)

def eca_ca(rule):
    # Symbols 0/u are exactly numerical states 0/1.
    def raw(c):
        if not c: return {}
        assert (rule&1)==0, 'Vacuum must be quiescent'
        candidates={y for x in c for y in (x-1,x,x+1)}
        return {x:'u' for x in candidates
                if (rule >> ((int(x-1 in c)<<2)|(int(x in c)<<1)|int(x+1 in c)))&1}
    one=raw({0:'u'})
    assert len(one)==1
    return CA(f'ECA_{rule}_comoving',1,{'u':1},raw,next(iter(one)))

def conservative_ecas():
    # Exact de Bruijn potential check: f(abc)-b = P(bc)-P(ab).
    # The sum telescopes on every periodic/finite-support configuration.
    good=[]
    for rule in range(256):
        potential={0:0}; consistent=True
        for _ in range(5):
            for a,b,c in product((0,1),repeat=3):
                u=2*a+b;v=2*b+c;difference=((rule>>(4*a+2*b+c))&1)-b
                if u not in potential: continue
                expected=potential[u]+difference
                if v in potential and potential[v]!=expected: consistent=False
                potential.setdefault(v,expected)
        if consistent and len(potential)==4: good.append(rule)
    assert good==[170,184,204,226,240],good
    return good

def integer_four_state_ca():
    # Labels u,2,3 denote numerical states 1,2,3, with vacuum0.
    def raw(c):
        centers={x for x,s in c.items() if s!='u'};proposals=[]
        for x in centers:
            if any(0<abs(x-y)<=4 for y in centers): continue
            removed={x};added=None
            if c[x]=='2':
                if c.get(x+1)=='u': removed.add(x+1);added={x:'3'}
                elif x+1 not in c: added={x+1:'2'}
            elif x-1 not in c and x+1 not in c: added={x-1:'u',x+1:'2'}
            if added is not None: proposals.append((removed,added))
        out=dict(c)
        for removed,added in proposals:
            for x in removed: del out[x]
            assert not(set(out)&set(added));out.update(added)
        return out
    return CA('integer_states_0_1_2_3',5,{'u':1,'2':2,'3':3},raw)

def typed_ca():
    weights={'u':1,**{s:2 for s in 'ALCDPQ'},'H':3,'K':3}
    def raw(c):
        # Centers of weight >=2 within distance4 suppress both updates.
        # Otherwise each rewrite is confined to [center-1,center+1],
        # consumes all occupied sites it changes, and preserves their mass.
        heavy={x for x,s in c.items() if s!='u'}
        proposals=[]
        for x in heavy:
            if any(0<abs(x-y)<=4 for y in heavy): continue
            s=c[x]; removed={x}; added=None
            if s in 'ALPQ':
                direction=-1 if s in 'LQ' else 1
                nxt=x+direction
                if c.get(nxt)=='u': removed.add(nxt); added={x:'H'}
                elif nxt not in c:
                    phase={'P':'Q','Q':'P'}.get(s,s)
                    added={nxt:phase}
            elif s=='D': added={x:'C'}
            elif s=='C' and x-1 not in c and x+1 not in c:
                added={x-1:'u',x+1:'u'}
            elif s in 'HK' and x-1 not in c and x+1 not in c:
                added={x-1:'u',x+1:('L' if s=='H' else 'A')}
            if added is not None: proposals.append((removed,added))
        out=dict(c)
        for removed,added in proposals:
            for x in removed: del out[x]
            assert not(set(out)&set(added))
            out.update(added)
        return out
    # Output site sees centers at distance1 and their exclusion tests at4.
    return CA('weighted_rewrite',5,weights,raw)

@dataclass
class Profile:
    configs: list
    mu: int
    period: int
    drift: int
    def at(self,k):
        if k<len(self.configs): return self.configs[k]
        n,r=divmod(k-self.mu,self.period)
        return shift(self.configs[self.mu+r],n*self.drift)

def profile(ca,c):
    seen={}; configs=[]
    while True:
        shape,a=norm(c)
        if shape in seen:
            mu,old=seen[shape]
            return Profile(configs,mu,len(configs)-mu,a-old)
        seen[shape]=(len(configs),a); configs.append(dict(c))
        assert span(c)<=2*ca.S, ('mass2 invariant',ca.name,c)
        c=ca.step(c)


def ceildiv(a,b): return -((-a)//b)

def first_linear_hit(A,D,lo,hi):
    """Smallest n>=0 with lo <= A+nD <= hi; None if absent."""
    if lo>hi: return None
    if D==0: return 0 if lo<=A<=hi else None
    if D<0: return first_linear_hit(-A,-D,-hi,-lo)
    n=max(0,ceildiv(lo-A,D))
    return n if A+n*D<=hi else None

def first_core(profile,b,B):
    candidates=[]
    for k in range(profile.mu):
        c=profile.configs[k]
        if max(max(c),b)-min(min(c),b)<=B: candidates.append(k)
    for r in range(profile.period):
        c=profile.configs[profile.mu+r]
        n=first_linear_hit(min(c),profile.drift,b-B,b+B-span(c))
        if n is not None: candidates.append(profile.mu+r+n*profile.period)
    return min(candidates) if candidates else None


def components(c,S):
    groups=[]
    for x in sorted(c):
        if not groups or x-max(groups[-1])>2*S: groups.append({})
        groups[-1][x]=c[x]
    return groups

class Accelerator:
    def __init__(self,ca,c):
        self.ca=ca; self.segments=[]; self.cycle=None; self.visits=0
        mass=sum(ca.weights[s] for s in c.values())
        self.mass=mass
        if mass==0: self.segments.append((0,None,lambda k:{})); return
        if mass<=2:
            if span(c)<=2*ca.S:
                p=profile(ca,c); self.segments.append((0,None,p.at))
            else:
                assert all(s=='u' for s in c.values())
                self.segments.append((0,None,lambda k,c=dict(c):c))
            return
        assert mass==3
        seen={}; t=0; B=4*ca.S
        while True:
            if span(c)<=B:
                shape,a=norm(c); self.visits+=1
                if shape in seen:
                    t0,a0=seen[shape]; self.cycle=(t0,t-t0,a-a0); return
                seen[shape]=(t,a)
                self.segments.append((t,1,lambda k,c=dict(c):c))
                c=ca.step(c); t+=1
                continue
            groups=components(c,ca.S)
            if len(groups)==3:
                assert all(s=='u' for s in c.values())
                self.segments.append((t,None,lambda k,c=dict(c):c)); return
            assert len(groups)==2
            pair=next(g for g in groups if sum(ca.weights[s] for s in g.values())==2)
            marker=next(g for g in groups if sum(ca.weights[s] for s in g.values())==1)
            b=next(iter(marker)); p=profile(ca,pair)
            def combined(k,p=p,b=b):
                out=dict(p.at(k)); assert b not in out; out[b]='u'; return out
            k=first_core(p,b,B)
            if k is None:
                self.segments.append((t,None,combined)); return
            assert k>0
            self.segments.append((t,k,combined)); c=combined(k); t+=k
    def at(self,t):
        offset=0
        if self.cycle and t>=self.cycle[0]:
            t0,p,d=self.cycle; n,r=divmod(t-t0,p);t=t0+r;offset=n*d
        for start,length,fun in reversed(self.segments):
            if t>=start and (length is None or t<start+length): return shift(fun(t-start),offset)
        raise AssertionError(('missing segment',t,self.segments))


def run():
    counts={'orbit_cases':0,'checked_time_steps':0,'core_cycles':0,'terminal_tails':0,
            'mass2_profiles':0,'linear_solver_cases':0,'dense_conservation_cases':0}
    for A,D,lo,hi in product(range(-4,5),range(-3,4),range(-4,5),range(-4,5)):
        got=first_linear_hit(A,D,lo,hi)
        expected=next((n for n in range(20) if lo<=A+n*D<=hi),None)
        assert got==expected,(A,D,lo,hi,got,expected)
        counts['linear_solver_cases']+=1
    eca_rules=conservative_ecas()
    cas=[right_ca(m,d) for m in range(8) for d in (-1,1)]+[eca_ca(r) for r in eca_rules]+[integer_four_state_ca(),typed_ca()]
    rng=random.Random(20261003)
    for ca in cas:
        # Checks on multi-center/dense cases also test the weighted rewrite guard.
        for _ in range(120):
            c={x:rng.choice(list(ca.weights)) for x in range(-10,11) if rng.random()<.4}
            ca.step(c); counts['dense_conservation_cases']+=1
        initial=[]
        for s,w in ca.weights.items():
            if w<=3: initial.append({-7:s})
            if w==2:
                for b in (-100,-31,-2,-1,1,2,31,100): initial.append({0:s,b:'u'})
        for d in range(1,2*ca.S+1):
            p=profile(ca,{0:'u',d:'u'}); counts['mass2_profiles']+=1
            cur={0:'u',d:'u'}
            for k in range(50): assert p.at(k)==cur;cur=ca.step(cur)
        for a,b in combinations(range(1,25),2): initial.append({0:'u',a:'u',b:'u'})
        for _ in range(30):
            xs=rng.sample(range(-150,151),3);initial.append(dict.fromkeys(xs,'u'))
        for c in initial:
            acc=Accelerator(ca,c); cur=dict(c)
            for t in range(160):
                assert acc.at(t)==cur,(ca.name,c,t,acc.at(t),cur)
                cur=ca.step(cur);counts['checked_time_steps']+=1
            counts['orbit_cases']+=1
            counts['core_cycles' if acc.cycle else 'terminal_tails']+=1
    # Binary pair travels +1 every2 steps, using h(left,right2)=left OR right2.
    moving=right_ca(7)
    p=profile(moving,{0:'u',1:'u'})
    assert p.period==2 and p.drift==1
    gap=10**30+17
    huge=Accelerator(moving,{0:'u',1:'u',gap:'u'})
    # Exact endpoint and first-entry formula; no iteration over the huge gap.
    assert first_core(p,gap,4*moving.S)==2*(gap-4*moving.S)
    for t in (0,1,10**20,2*(gap-8)-1,2*(gap-8),2*gap+100,10**40):
        out=huge.at(t); assert len(out)==3
    counts['huge_gap']=str(gap)
    counts['huge_gap_core_visits']=huge.visits
    counts['rules_tested']=len(cas)
    counts['exactly_certified_conservative_eca_rules']=eca_rules
    counts['status']='PASS'
    return counts

if __name__=='__main__':
    result=run()
    target=Path(__file__).with_name('test-results.json')
    target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
