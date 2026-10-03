#!/usr/bin/env python3
"""Independent sparse expansion, exact rational tests, and finite LP branches.

Tests are finite evidence, not a proof of the all-real theorem. SymPy's simplex
uses rational arithmetic; every returned point is independently substituted.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import argparse, hashlib, json, random
from real_certificate import RealCompiler, Prism, PeriodicInput, base, BASE_SHA256

# Independent polynomial engine. Does not call Summand.records().
def plus(*polys):
    d=Counter()
    for p in polys:
        for m,c in p.items():d[m]+=c
    return {m:c for m,c in d.items() if c}
def times(a,b):
    d=Counter()
    for m,c in a.items():
        for n,k in b.items():d[tuple(sorted(m+n))]+=c*k
    return {m:c for m,c in d.items() if c}
def sc(k,a):return {m:k*c for m,c in a.items() if k*c}
def cn(k):return {():k} if k else {}
def vv(i):return {(i,):1}
def sq(p):return times(p,p)
def independent_polynomial(C,variant):
    P=C.P;source=C.source;out=[]
    def v(p,f):return vv(C.v(p,f))
    def e(p,q,f):return vv(C.ev(p,q,f))
    def u(p):return plus(v(p,'k'),v(p,'c'))
    def r(p):return plus(v(p,'k'),sc(2,v(p,'c')),v(p,'beta'))
    for p in P.points():
        z,ell,f,k,c,b,g,h=(v(p,n) for n in base.FIELDS)
        A=[];B=[]
        for q in P.neighbors(p):
            A += [e(p,q,x) for x in (('eq','pos','hi') if p<q else ('lo','neg','eq'))]
            B += [e(p,q,x) for x in (('neg','eq','pos','hi') if p<q else ('lo','neg','eq','pos'))]
        A=plus(*A);B=plus(*B)
        out += [sq(plus(z,sc(6,u(p)),*(sc(-1,u(q)) for q in P.neighbors(p)),cn(-source.height(p)))),sq(plus(z,ell,cn(-5))),sq(plus(f,k,c,cn(-1))),times(plus(f,k),b),times(u(p),sq(plus(z,sc(-1,A),sc(-1,g)))),times(f,plus(g,u(p)) if variant in ('flat','merged') else g),times(c,sq(plus(B,sc(-1,z),cn(-1),sc(-1,h)))),times(plus(f,k),h)]
        if variant=='sharp':out.extend(times(a,b) for a,b in combinations((f,k,c),2))
    for p,q in P.edges():
        a,b,c,d,e_,gap=(e(p,q,x) for x in base.EDGE_FIELDS);delta=plus(r(q),sc(-1,r(p)))
        out.append(sq(plus(a,b,c,d,e_,cn(-1))))
        out.extend(times(weight,sq(res)) for weight,res in ((a,plus(delta,cn(2),gap)),(b,plus(delta,cn(1))),(c,delta),(d,plus(delta,cn(-1))),(e_,plus(delta,cn(-2),sc(-1,gap)))))
        out.append(times(plus(b,c,d),gap))
        if variant=='sharp':out.extend(times(x,y) for x,y in combinations((a,b,c,d,e_),2))
    for j,(x,p) in enumerate(P.halo()):
        out.append(sq(plus(u(p),vv(8*P.V+6*P.E+j),cn(source.height(x)-5))))
    return plus(*out)
def pol_value(poly,w):
    return sum(c*__import__('functools').reduce(lambda a,i:a*w[i],m,F(1)) for m,c in poly.items())
def check(condition,message):
    if not condition:raise AssertionError(message)

def expansion_checks():
    rng=random.Random(260310);cases=[];valid=invalid=mutations=0
    for dims in ((1,1,1),(2,1,1),(3,1,1),(2,2,1),(2,2,2),(3,2,1)):
      for bg in (0,4,5):
        P=Prism((-2,3,-1),dims)
        source=PeriodicInput((1,1,1),(bg,),((P.point(0),rng.randrange(0,14)),))
        C=base.Compiler(P,source);orig=C.polynomial();ind=independent_polynomial(C,'base')
        check(orig==ind,'independent base expansion mismatch')
        row={'dims':dims,'background':bg,'original_monomials':len(orig),'original_raw':C.ledger()['records']}
        for mode in ('merged','flat','sharp'):
            D=RealCompiler(P,source,mode);poly=D.polynomial();expected=independent_polynomial(D,mode)
            check(poly==expected,'independent modified expansion mismatch')
            check(set(orig)==set(poly),'changed monomial support')
            check(dict(D.collected_records())==poly,'local collected stream mismatch')
            check(max(map(len,poly))==3,'degree not exactly cubic')
            check(len(set(D.penalty_monomials()))==len(list(D.penalty_monomials())),'penalty duplicate')
            delta=plus(poly,sc(-1,orig));check(delta=={m:1 for m in D.penalty_monomials()},'incorrect modification')
            for p in P.points():
                check(orig[tuple(sorted((D.v(p,'f'),D.v(p,'k'))))]==2,'fk coefficient')
                check(orig[tuple(sorted((D.v(p,'f'),D.v(p,'c'))))]==2,'fc coefficient')
                check(orig[tuple(sorted((D.v(p,'k'),D.v(p,'c'))))]==86,'kc coefficient')
            for p,q in P.edges():
                for a,b in combinations(base.EDGE_FIELDS[:5],2):
                    check(orig[tuple(sorted((D.ev(p,q,a),D.ev(p,q,b))))]==2,'edge pair coefficient')
            if mode in ('merged','flat'):check(max(map(abs,poly.values()))==max(map(abs,orig.values())),'height changed')
            actual,closed=D.ledger(),D.closed_ledger()
            for key in ('summands','records','evaluation_adds','evaluation_mults','expansion_coefficient_mults','witnesses','plain_square_residuals','weighted_square_residuals','product_summands'):
                check(actual[key]==closed[key],f'ledger mismatch {mode} {key}')
            w=[F(rng.randrange(0,17),rng.randrange(1,9)) for _ in range(P.witnesses)]
            check(D.evaluate_orthant(w)==pol_value(poly,w),'rational evaluation mismatch')
            check(all(t.value(w)>=0 for t in D.summands()),'negative orthant summand')
            row[mode]={'raw':actual['records'],'summands':actual['summands'],'evaluation_mults':actual['evaluation_mults'],'evaluation_adds':actual['evaluation_adds'],'expansion_mults':actual['expansion_coefficient_mults']}
        try:w=C.certificate()
        except ValueError:invalid+=1
        else:
            valid+=1
            for mode in ('merged','flat','sharp'):
                D=RealCompiler(P,source,mode);check(D.evaluate_orthant(w)==0,'natural witness lost')
                for i in range(len(w)):
                    for offset in (F(1,2),F(-1,2)):
                        if w[i]+offset<0:continue
                        v=list(w);v[i]+=offset
                        check(D.evaluate_orthant(v)>0,'nontrivial rational mutation still zero');mutations+=1
        cases.append(row)
    # Published spurious real zero of the old cubic, now excluded exactly.
    P=Prism((0,0,0),(1,1,1));src=PeriodicInput((1,1,1),(0,),(((0,0,0),1),));C=base.Compiler(P,src)
    w=[F(0),F(5),F(5,6),F(1,6),F(0),F(0),F(0),F(0)]+[F(29,6)]*6
    check(sum(t.value(w) for t in C.summands())==0,'old counterexample broken')
    counter={m:str(RealCompiler(P,src,m).evaluate_orthant(w)) for m in ('merged','flat','sharp')}
    check(set(counter.values())=={'5/36'},'old counterexample not excluded')
    return {'cases':cases,'valid_natural_witnesses':valid,'nonbinary_or_halo_rejections':invalid,'rational_single_coordinate_mutations':mutations,'old_fractional_zero_new_values':counter}

# Exact support-pattern branch solver for all real nonnegative zeros on selected
# tiny instances. Once a category support and edge selector are fixed, the
# vanishing-summand conditions are affine; strict support is encoded by a common
# margin t>0, found by maximizing t with t<=1. This independently searches mixed
# category branches rather than assuming the integrality theorem.
def branch_search(heights,variant):
    if variant not in ('base','merged','flat'):raise ValueError('branch search supports base, merged, flat')
    from sympy import Matrix, Rational, S
    from sympy.solvers.simplex import lpmin, InfeasibleLPError
    P=Prism((0,0,0),(len(heights),1,1));src=PeriodicInput((1,1,1),(0,),tuple((P.point(i),h) for i,h in enumerate(heights)))
    C=RealCompiler(P,src,variant) if variant!='base' else base.Compiler(P,src)
    n=P.witnesses;t=n;N=n+1;solutions=[];attempts=infeasible=zero_margin=0
    patterns=[p for size in (1,2,3) for p in combinations(('f','k','c'),size)]
    for cats in product(patterns,repeat=P.V):
      if variant!='base' and any('f' in pat and len(pat)>1 for pat in cats):continue
      for selections in product(range(5),repeat=P.E):
        attempts+=1;eq=[];rhs=[];A=[];b=[]
        def equality(dic):
            eq.append([dic.get(i,0) for i in range(N)]);rhs.append(-dic.get(-1,0))
        for p,pat in zip(P.points(),cats):
            for f in ('f','k','c'):
                i=C.v(p,f)
                if f not in pat:equality({i:1})
                else:
                    row=[0]*N;row[i]=-1;row[t]=1;A.append(row);b.append(0)
        for (p,q),sel in zip(P.edges(),selections):
            for j,f in enumerate(base.EDGE_FIELDS[:5]):equality({C.ev(p,q,f):1,-1:-int(j==sel)})
        # Process original zero terms using the chosen strictly-positive supports.
        for term in base.Compiler(P,src).summands():
            if term.kind=='square':
                if term.weight is None:equality(term.residual)
                else:
                    positive=False
                    for i,coef in term.weight.items():
                        if i<8*P.V:
                            v,f=divmod(i,8);positive |= base.FIELDS[f] in cats[v]
                        else:
                            e,f=divmod(i-8*P.V,6);positive |= f==selections[e]
                    if positive:equality(term.residual)
            else:
                # All three vertex product families have first factor support
                # known from the category; edge inactive_gap uses selector.
                active=False
                for i in term.residual:
                    if i<8*P.V:
                        v,f=divmod(i,8);active |= base.FIELDS[f] in cats[v]
                    else:
                        e,f=divmod(i-8*P.V,6);active |= f==selections[e]
                if active:equality(term.weight)
        row=[0]*N;row[t]=1;A.append(row);b.append(1)
        # Eliminate equalities exactly first. Direct SymPy linprog(A_eq=...)
        # returned a residual-invalid point for an infeasible branch during
        # development; independent substitution caught it. Reduced affine
        # inequalities avoid that observed failure, and outputs are still checked.
        try:affine_solution,params=Matrix(eq).gauss_jordan_solve(Matrix(rhs))
        except ValueError:infeasible+=1;continue
        constraints=[x>=0 for x in affine_solution]
        constraints += [sum(a*x for a,x in zip(row,affine_solution))<=val for row,val in zip(A,b)]
        if any(x is S.false for x in constraints):infeasible+=1;continue
        constraints=[x for x in constraints if x is not S.true]
        try:value,substitution=lpmin(-affine_solution[t],constraints)
        except InfeasibleLPError:infeasible+=1;continue
        solution=[x.subs(substitution) for x in affine_solution]
        check(all(not x.free_symbols for x in solution),'LP left free symbols')
        if solution[t]<=0:zero_margin+=1;continue
        w=[F(x) for x in solution[:n]]
        check(all(sum(a*x for a,x in zip(row,solution))==val for row,val in zip(eq,rhs)),f'LP equality violation {heights} {variant} cats={cats} sel={selections} violations='+str([(sum(a*x for a,x in zip(row,solution)),val) for row,val in zip(eq,rhs) if sum(a*x for a,x in zip(row,solution))!=val]))
        check(all(x>=0 for x in solution),'LP nonnegative violation')
        check(all(sum(a*x for a,x in zip(row,solution))<=val for row,val in zip(A,b)),'LP inequality violation')
        if variant!='base':check(all(not x.free_symbols for x in affine_solution[:n]),'modified branch has affine free coordinates')
        total=sum(term.value(w) for term in C.summands());check(total==0,'LP candidate failed substitution')
        solutions.append({'categories':cats,'edge_cases':selections,'margin':str(solution[t]),'affinely_unique_witness':all(not x.free_symbols for x in affine_solution[:n]),'integral':all(x.denominator==1 for x in w),'witness':[str(x) for x in w]})
    if variant!='base':
        check(all(s['integral'] for s in solutions),'fractional modified zero')
        try:canonical=C.certificate()
        except ValueError:check(not solutions,'zero where certificate rejects')
        else:
            check(len(solutions)==1,'wrong feasible branch count')
            check([F(x) for x in solutions[0]['witness']]==canonical,'zero differs from canonical')
    return {'heights':heights,'variant':variant,'attempts':attempts,'solver_or_elimination_rejections':infeasible,'zero_margin':zero_margin,'solutions':solutions}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--skip-branches',action='store_true');ap.add_argument('--output',default='verification.json');args=ap.parse_args()
    result={'base_sha256':BASE_SHA256,'test_scope':'Finite rational computations corroborate, do not prove, the general theorem. Feasible candidates are independently rechecked; LP rejections have no independently checked Farkas certificate.','expansion':expansion_checks()}
    if not args.skip_branches:
        result['exact_real_branch_search']=[branch_search(h,mode) for h,mode in [([1],'base'),([0],'merged'),([1],'merged'),([6],'merged'),([12],'merged'),([5,5],'merged'),([6,5],'merged'),([6,6],'merged'),([6,5,5],'merged')]]
    text=json.dumps(result,indent=2,sort_keys=True);Path(args.output).write_text(text+'\n');print(json.dumps({'status':'pass','output':args.output,'expansion_cases':len(result['expansion']['cases']),'branch_cases':len(result.get('exact_real_branch_search',[])),'sha256':hashlib.sha256((text+'\n').encode()).hexdigest()}))
if __name__=='__main__':main()
