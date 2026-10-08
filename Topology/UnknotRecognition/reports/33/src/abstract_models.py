"""Independent reversible Boolean models for exhaustive theorem checks."""
from dataclasses import dataclass
from layered_search import Action

@dataclass(frozen=True)
class Rule:
    toggle: int
    guard: int
    value: int
    def support(self): return self.toggle|self.guard
    def legal(self,x): return x&self.guard==self.value

class BooleanSystem:
    def __init__(self,rules,target=None): self.rules=tuple(rules); self.target=target
    def actions(self,x):
        for i,r in enumerate(self.rules):
            if r.legal(x):
                yield Action((i,),frozenset(j for j in range(r.support().bit_length())
                                           if (r.support()>>j)&1),r.toggle)
    def apply(self,x,a):
        r=self.rules[a.key[0]]
        if not r.legal(x): raise ValueError("illegal Boolean action")
        return x^r.toggle
    def goal(self,x): return True if self.target is not None and self.target(x) else None

def brute_endpoints(system,initial,depth,births):
    # This oracle does not use normal forms. It tracks every support history.
    endpoints={initial}; stack=[(initial,frozenset(),0,0)]
    traces=0
    while stack:
        x,active,b,used=stack.pop()
        if used==depth: continue
        for a in system.actions(x):
            b2=b+active.isdisjoint(a.footprint)
            if b2>births: continue
            y=system.apply(x,a); endpoints.add(y); traces+=1
            stack.append((y,active|a.footprint,b2,used+1))
    return endpoints,traces
