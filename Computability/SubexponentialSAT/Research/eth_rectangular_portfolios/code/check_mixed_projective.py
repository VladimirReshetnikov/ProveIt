"""Independent finite checks of authored mixed-root kernels; stdlib only."""
import json
import random
import sys
from itertools import product
from math import prod
from pathlib import Path
from mixed_projective import Ring,root15,root15_bitwise,checked_powers,projective,centered,direct,adaptive,affine,gray


def demand(ok,message):
    if not ok: raise ArithmeticError(message)


def compositions(n,k):
    if k==1:
        yield (n,); return
    for a in range(n+1):
        for rest in compositions(n-a,k-1): yield (a,)+rest


def run():
    rng=random.Random(271027)
    roots=0; identities=0; monomials=0; gray_cases=0; rejects=0; affine_cases=0
    for ell in (1,2):
        for p in (1,2,3,7,17,32):
            ring=Ring(p,ell); root=root15(ring); powers=checked_powers(ring,root)
            demand(root==root15_bitwise(ring),'doubling versus bitwise lift')
            for q in (3,5):
                for m in range(q):
                    total=ring.zero
                    for g in range(q): total=ring.add(total,powers[(15*g*m//q)%15])
                    demand(total==ring.scale(ring.one,q) if m==0 else total==ring.zero,'orthogonality')
            roots+=1
    # Independent monomial congruence proof enumeration, no extractor call.
    for t in range(2,5):
        for beta in product(range(1,5),repeat=t):
            k=min(range(t),key=beta.__getitem__)
            qs=[3 if b<=2 else 5 for b in beta]
            for alpha in compositions(sum(beta),t):
                survives=all((alpha[j]-beta[j])%qs[j]==0 for j in range(t) if j!=k)
                demand(survives==(alpha==beta),'mixed alias')
                monomials+=1
    for radices in product(range(1,6),repeat=3):
        points=[]; previous=None
        for point,j,step in gray(radices):
            now=tuple(point)
            if previous is not None:
                demand(sum(a!=b for a,b in zip(now,previous))==1,'Gray support')
                demand(now[j]-previous[j]==step and abs(step)==1,'Gray step')
            points.append(now);previous=now
        demand(len(points)==prod(radices)==len(set(points)),'Gray coverage');gray_cases+=1
    # Quotient/nilpotent ring cases, including zero targets and odd profiles.
    profiles=[(),(0,),(1,),(2,),(4,),(0,2,2),(1,1),(1,2),(2,2),
              (1,3),(2,4),(4,4),(1,1,2),(2,2,2),(2,2,4),
              (2,2,4,4),(1,2,3),(1,1,1,1),(2,1,4)]
    for ell in (1,2):
        for p in (1,3,13):
            ring=Ring(p,ell); root=root15(ring)
            for beta in profiles:
                for trial in range(3):
                    rows=[[tuple(rng.randrange(-7,12) for _ in range(4*ell))
                           for b in beta] for _ in range(sum(beta))]
                    want=direct(rows,beta,ring)
                    for algorithm in ('mixed','common','centered','adaptive'):
                        stats={}
                        if algorithm=='mixed': got=projective(rows,beta,ring,root,True,stats)
                        elif algorithm=='common': got=projective(rows,beta,ring,root,False,stats)
                        elif algorithm=='centered': got=centered(rows,beta,ring,stats)
                        else: got=adaptive(rows,beta,ring,root,stats)
                        demand(got==want,f'coefficient {ell,p,beta,trial,algorithm}');identities+=1
                        if algorithm=='centered' and sum(beta)>0:
                            demand(stats['evaluations']==prod(b+1 for b in beta)//2,'half count')
    # Exhaustive scalar-valued 4-row 2-column inputs, embedded in same quotient.
    ring=Ring(5);root=root15(ring)
    for entries in product((0,1),repeat=8):
        rows=[entries[i:i+2] for i in range(0,8,2)]
        want=direct(rows,(2,2),ring)
        demand(projective(rows,(2,2),ring,root)==want,'binary mixed')
        demand(centered(rows,(2,2),ring)==want,'binary centered');identities+=2
    # Invalid roots must not be mistaken for orthogonal characters.
    for invalid in (ring.one,ring.zero,ring.canon((0,1,0,0))):
        try: projective([[1,1]]*4,(2,2),ring,invalid)
        except ValueError: rejects+=1
        else: raise ArithmeticError('invalid root accepted')
    for beta,rows in [((-1,2),[[1,1]]),((1,1),[[1]]),((5,1),[[1,1]]*6),((True,1),[[1,1]]*2)]:
        try: projective(rows,beta,ring,root)
        except ValueError: rejects+=1
        else: raise ArithmeticError('invalid input accepted')
    # Nonminimal fixed coordinate / inadequate orders would alias this monomial.
    beta=(1,3);alpha=(4,0)
    demand((alpha[0]-beta[0])%3==0 and alpha!=beta,'negative alias control')
    for R in range(6):
        for beta in product(range(4),repeat=2):
            rows=[[rng.randrange(-3,4) for _ in range(3)] for _ in range(R)]
            want=direct(rows,(R-sum(beta),)+beta,ring) if sum(beta)<=R else ring.zero
            demand(affine(rows,beta,ring,root)==want,'affine adapter');affine_cases+=1
    result=dict(status='PASS',python_optimized=not __debug__,root_lifts=roots,
                coefficient_equalities=identities,monomial_alias_checks=monomials,
                gray_grids=gray_cases,rejections=rejects,
                affine_adapter_equalities=affine_cases,
                doubling_bitwise_root_equalities=roots,
                scope='Finite exact component checks, not a full SAT solver or formal theorem proof')
    return result


if __name__=='__main__':
    result=run();text=json.dumps(result,indent=2)
    if len(sys.argv)>1: Path(sys.argv[1]).write_text(text+'\n')
    print(text)
