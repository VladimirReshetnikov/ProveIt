"""Independent local soundness audit of AFFINE constructed predecessor supply.
Not a formal proof; sampled standard-model checking of each emitted equation
at zero value for the freshly allocated parameter, including malformed data.
"""
import itertools, json, random
from pathlib import Path

class Reject(Exception): pass
class Budget(Exception): pass

# Exact opening function, implemented readably and with an explicit floor.
def opening(a, image=None, depth=0, floor=-2, fuel=180):
    if fuel <= 0: raise Budget
    if isinstance(a,list):
        inc=len(a)+1
        return [opening(b,image,depth+inc,floor,fuel-1) for b in a]
    if floor <= a < depth: return a
    return opening(image,depth=1,floor=floor,fuel=fuel-1) if depth%2 else 0

# Mathematical decoder from the report, separate from opening implementation.
def number(a,env,valuation,budget):
    budget[0]-=1
    if budget[0]<=0:raise Budget
    if not isinstance(a,list):
        a=int(a//1)
        if a < 0:
            return valuation[int(a//1)]
        j=int((a-1)//2)
        return 0 if a==0 else env[j]
    if len(a)==0 or len(a)==2:return 0
    if len(a)==1:return 1+number(a[0],(0,)+env,valuation,budget)
    if len(a)!=3:return 0
    counter,seed,body=a
    n=number(counter,(0,0)+env,valuation,budget)
    v=number(seed,(0,0)+env,valuation,budget)
    if n>12:raise Budget
    for _ in range(n):v=number(body,(v,v)+env,valuation,budget)
    return v

def generate(s,flag):
    pred,seed,body=s
    raw=[[flag and [pred],seed,body],opening(body,s,1) if flag else seed]
    return opening(raw,-3,floor=-3)

rng=random.Random(20261110)
scalars=[-4,-3,-2,-1,0,1,2,3,4,5,6,7,8,9,10,11,12,0.5,2.5,-1.5]
def tree(depth):
    if depth==0 or rng.random()<.45:return rng.choice(scalars)
    arity=rng.randrange(7)
    return [tree(depth-1) for _ in range(arity)]

def main():
    vals=[{-3:0,-2:x,-1:y} for x in range(3) for y in range(3)]
    # Exhaustive leaf/binder-boundary tests, then arbitrary small raw trees.
    terms=scalars+[[],[0],[1],[2],[3],[4],[5],[6],[7],[-1],[0,0],[1,2]]
    cases=itertools.chain(itertools.product(terms,scalars,terms), ((tree(3),tree(3),tree(3)) for _ in range(18000)))
    attempted=accepted=valuations=bounded=0
    for pred,seed,body in cases:
        for flag in (0,1):
            attempted+=1
            try:h=generate([pred,seed,body],flag)
            except (TypeError,ValueError,IndexError,RecursionError,KeyError,Reject):continue
            except Budget:bounded+=1;continue
            accepted+=1
            for v in vals:
                try:
                    left=number(h[0],(0,),v,[12000]);right=number(h[1],(0,),v,[12000])
                except Budget:bounded+=1;continue
                except Exception as e:raise AssertionError(('decoder error',pred,seed,body,flag,h,v,type(e).__name__)) from e
                assert left==right, (pred,seed,body,flag,h,v,left,right)
                valuations+=1
    result={'attempted_generator_packets':attempted,'successful_generations':accepted,'checked_standard_model_valuations':valuations,'resource_bounded_cases':bounded,'result':'PASS','seed':20261110,'scope':'local Supply rule only; not a proof of universal soundness or biinterpretability'}
    (Path(__file__).resolve().parents[1] / 'evidence/supply_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
