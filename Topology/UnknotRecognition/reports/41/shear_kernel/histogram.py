"""Multiplier-run histograms and direct, already-reduced output construction."""
from __future__ import annotations
from collections import Counter
from dataclasses import dataclass
from .slp import Grammar

@dataclass
class Profile:
    multiplier: int
    constant: int
    # (left retained letter, inverse of right retained letter, signed a exponent)
    gaps: dict[tuple[int,int,int],int]
    summaries: dict[int,tuple[int,int,int,int]]
    reachable: list[int]

    @property
    def original_length(self) -> int:
        return self.constant+sum(w*abs(e) for (_,_,e),w in self.gaps.items())

    def value(self, z: dict[int,int]) -> int:
        return self.constant+sum(w*abs(e+z.get(u,0)-z.get(v,0))
                                 for (u,v,e),w in self.gaps.items())

def summarize(g: Grammar, roots: list[int], a: int) -> tuple[list[int],dict]:
    if type(a) is not int or a==0: raise ValueError('nonzero signed multiplier')
    g.validate_roots(roots)
    reach=g.reachable(roots); ends={0:(0,0,0,0)}
    for n in reach:
        q=g.rules[n]
        if q[0]=='t':
            x=q[1]; e=1 if x==a else -1
            ends[n]=(0,0,e,e) if abs(x)==abs(a) else (x,x,0,0)
        elif q[0]=='c':
            f,l,p,s=ends[q[1]]; h,j,t,v=ends[q[2]]
            ends[n]=(f or h,j or l,p if f else p+t,v if j else s+v)
        else:
            f,l,p,s=ends[q[1]]; k=q[2]
            ends[n]=(f,l,p,s) if f else (0,0,k*p,k*p)
    return reach,ends

def profile(g: Grammar, roots: list[int], a: int) -> Profile:
    reach,ends=summarize(g,roots,a); counts=Counter(roots); hist=Counter(); constant=0
    for root in roots:
        f,l,p,s=ends[root]
        if f: hist[(l,-f,s+p)] += 1
        else: constant += g.meta[root].length
    for n in reversed(reach):
        q=g.rules[n]; w=counts[n]
        if q[0]=='t':
            if abs(q[1])!=abs(a): constant+=w
        elif q[0]=='c':
            x,y=q[1:]; counts[x]+=w; counts[y]+=w
            if ends[x][1] and ends[y][0]:
                hist[(ends[x][1],-ends[y][0],ends[x][3]+ends[y][2])] += w
        else:
            x,k=q[1:]; counts[x]+=w*k
            f,l,p,s=ends[x]
            if f: hist[(l,-f,s+p)] += w*(k-1)
    return Profile(a,constant,dict(sorted((q,w) for q,w in hist.items() if w)),ends,reach)

def reference_profile(g: Grammar, roots: list[int], a: int) -> Profile:
    """Independent bottom-up multiset recurrence; intentionally quadratic space.

    Used by the certificate verifier. It does not call the reverse-weighted
    producer profile or its summary function.
    """
    g.validate_roots(roots); reach=g.reachable(roots)
    # first,last,prefix,suffix,non-a count,internal histogram
    tab={0:(0,0,0,0,0,Counter())}
    for n in reach:
        q=g.rules[n]
        if q[0]=='t':
            x=q[1]
            if abs(x)==abs(a):
                e=1 if x==a else -1; tab[n]=(0,0,e,e,0,Counter())
            else: tab[n]=(x,x,0,0,1,Counter())
        elif q[0]=='c':
            x,y=tab[q[1]],tab[q[2]]; h=x[5]+y[5]
            if x[1] and y[0]: h[(x[1],-y[0],x[3]+y[2])]+=1
            tab[n]=(x[0] or y[0],y[1] or x[1],x[2] if x[0] else x[2]+y[2],
                    y[3] if y[1] else x[3]+y[3],x[4]+y[4],h)
        else:
            x=tab[q[1]]; k=q[2]; h=Counter({e:w*k for e,w in x[5].items()})
            if x[0]:
                h[(x[1],-x[0],x[3]+x[2])]+=k-1
                tab[n]=(*x[:4],x[4]*k,h)
            else: tab[n]=(0,0,x[2]*k,x[2]*k,0,h)
    hist=Counter(); constant=0
    for root in roots:
        x=tab[root]; hist.update(x[5]); constant+=x[4]
        if x[0]: hist[(x[1],-x[0],x[3]+x[2])]+=1
        else: constant+=g.meta[root].length
    return Profile(a,constant,dict(sorted(hist.items())),{n:x[:4] for n,x in tab.items()},reach)

def reduced_image(g: Grammar, roots: list[int], p: Profile,
                  z: dict[int,int]) -> tuple[Grammar,list[int]]:
    """Construct cyclic representatives of a shear image without free reduction."""
    out=Grammar(); core={0:0}; ends=p.summaries; a=p.multiplier
    for n in p.reachable:
        q=g.rules[n]
        if q[0]=='t': core[n]=0 if abs(q[1])==abs(a) else out.letter(q[1])
        elif q[0]=='c':
            x,y=q[1:]; f=ends[x][1]; h=ends[y][0]
            if f and h:
                e=ends[x][3]+ends[y][2]+z.get(f,0)-z.get(-h,0)
                core[n]=out.concat(out.concat(core[x],out.run(a,e)),core[y])
            else: core[n]=core[x] or core[y]
        else:
            x,k=q[1:]; f,l,pref,suf=ends[x]
            if not f: core[n]=0
            else:
                e=suf+pref+z.get(l,0)-z.get(-f,0)
                block=out.concat(core[x],out.run(a,e))
                core[n]=out.concat(out.power(block,k-1),core[x])
    new=[]
    for root in roots:
        f,l,pref,suf=ends[root]
        if not f: new.append(out.run(a,pref))
        else:
            e=suf+pref+z.get(l,0)-z.get(-f,0)
            new.append(out.concat(core[root],out.run(a,e)))
    out.validate_roots(new)
    if sum(out.meta[x].length for x in new)!=p.value(z):
        raise AssertionError('direct output length disagrees with exact profile')
    return out,new
