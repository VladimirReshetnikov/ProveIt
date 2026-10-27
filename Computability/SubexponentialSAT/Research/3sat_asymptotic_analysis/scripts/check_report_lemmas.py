#!/usr/bin/env python3
"""Small exact checks of two elementary report lemmas, not a SAT algorithm."""
import itertools, json, math, sys
from fractions import Fraction

def require(condition, message):
    if not condition: raise ValueError(message)

def envelope():
    cases=0; selections=0
    for q in range(1,9): # u=q^2 makes all floor operations exact
      u=q*q
      for D in range(4*q,16*q+1,q):
        for multiple in range(2,10):
          M=multiple*D; K=M//D; B=D//(2*q); P=Fraction(M*D,u)
          require(Fraction(K*B*(B+1),2)<P,'budget failure')
          require(Fraction(M,8*q)<=K*B<=Fraction(M,2*q)<=M,'degree failure')
          cases+=1
          if K*B<=12:
            weights=[j for j in range(1,B+1) for _ in range(K)]
            for bits in itertools.product((0,1),repeat=len(weights)):
              require(sum(w*b for w,b in zip(weights,bits))<P,'selection failure')
              require(sum(bits)<=M,'ordinary degree failure'); selections+=1
    return {'parameter_cases':cases,'explicit_binary_selections':selections}

def degree_obstruction():
    systems=0
    for n in range(1,5):
      # Every affine polynomial on n variables, encoded by constant/linear bits.
      polys=list(range(1<<(n+1)))
      def deg(p): return 1 if p>>1 else 0
      def val(p,x): return (p&1)^((p>>1 & x).bit_count()&1)
      for p,q in itertools.product(polys,repeat=2):
        if deg(p)+deg(q)>=n: continue
        count=sum(val(p,x)==0 and val(q,x)==0 for x in range(1<<n))
        require(count%2==0,'odd solution count below total-degree threshold')
        systems+=1
    return {'affine_systems':systems,'declared_variables':[1,4]}

if __name__=='__main__':
    print(json.dumps({'status':'PASS','python_optimization_level':sys.flags.optimize,
        'envelope':envelope(),'degree_obstruction':degree_obstruction(),
        'scope':'Finite exact checks only; neither a theorem prover nor a faster SAT solver.'},indent=2))
