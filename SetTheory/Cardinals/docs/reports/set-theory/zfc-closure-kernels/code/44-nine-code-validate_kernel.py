#!/usr/bin/env python3
"""Independent finite checks for the arithmetic FC15 reference.

These checks validate encodings and finite transformations; they do not
prove FC15 consistent and do not verify a compiled binary machine.
"""
from itertools import product
import json
from pathlib import Path
import random
import time
import ground_kernel as K

def require(condition,message):
    if not condition:
        raise RuntimeError(message)

def finite_closure_checks():
    """Check all 262404 pairs of E/R graphs on 1,2,3 labels.

    Independently compute the EPSC implication, then construct Skolem
    witnesses and evaluate every one of the six actual closure clauses.
    D is one common member selector, independent of the chosen relation R.
    """
    checked=accepted=bounded=hulls=0
    by_size=[]
    for n in (1,2,3):
        totals={'n':n,'graph_pairs':0,'epsc_true':0,'locally_bounded':0,'has_hull':0}
        for ebits in range(1<<(n*n)):
            def e(x,y):
                return bool(ebits&(1<<(x*n+y)))
            members=[sum(1<<z for z in range(n) if e(z,y)) for y in range(n)]
            empties=[x for x in range(n) if members[x]==0]
            subs=[[not(members[y]&~members[u]) for u in range(n)] for y in range(n)]
            D=[next((z for z in range(n) if e(z,x)),0) for x in range(n)]
            for rbits in range(1<<(n*n)):
                totals['graph_pairs']+=1
                def r(x,y):
                    return bool(rbits&(1<<(x*n+y)))
                sb=all(any(all(not r(x,y) or subs[y][u] for y in range(n))
                           for u in range(n)) for x in range(n))
                valid_hulls=[]
                for h in range(n):
                    closed=all(not((x in empties or e(x,h)) and r(x,y)) or e(y,h)
                               for x in range(n) for y in range(n))
                    support=all(not e(y,h) or any(r(x,y) for x in range(n)) for y in range(n))
                    if closed and support:
                        valid_hulls.append(h)
                epsc=(not sb) or bool(valid_hulls)
                totals['locally_bounded']+=sb
                totals['has_hull']+=bool(valid_hulls)
                totals['epsc_true']+=epsc
                if not epsc:
                    # The false branch must have no bad-fiber witness;
                    # the true branch has no hull even with exact D.
                    require(all(any(all(not r(x,y) or subs[y][u] for y in range(n))
                                    for u in range(n)) for x in range(n)), 'negative SB')
                    continue
                flag=sb
                if flag:
                    h=valid_hulls[0]
                    ss=[next((x for x in range(n) if r(x,y)),0) for y in range(n)]
                    ff=0; yy=[0]*n; zz=[0]*n
                else:
                    h=0; ss=[0]*n
                    ff=next(x for x in range(n)
                            if all(any(r(x,y) and e(z,y) and not e(z,u)
                                       for y in range(n) for z in range(n)) for u in range(n)))
                    yz=[next((y,z) for y in range(n) for z in range(n)
                             if r(ff,y) and e(z,y) and not e(z,u)) for u in range(n)]
                    yy=[v[0] for v in yz]; zz=[v[1] for v in yz]
                # Share the two witnesses by the very same branch key.
                HH=h if flag else ff
                YY=ss if flag else yy
                # Direct truth evaluations of the actual fused clauses10..15.
                for u in range(n):
                    require(flag or r(HH,YY[u]),'clause10')
                    require(flag or e(zz[u],YY[u]),'clause11')
                    require(flag or not e(zz[u],u),'clause12')
                for x in range(n):
                    for y in range(n):
                        require(not flag or not e(x,HH) or not r(x,y) or e(y,HH),'clause13')
                        require(not flag or e(D[x],x) or not r(x,y) or e(y,HH),'clause14')
                for y in range(n):
                    require(not flag or not e(y,HH) or r(YY[y],y),'clause15')
        checked+=totals['graph_pairs'];accepted+=totals['epsc_true']
        bounded+=totals['locally_bounded'];hulls+=totals['has_hull']
        by_size.append(totals)
    return {'graph_pairs':checked,'epsc_true':accepted,'locally_bounded':bounded,
            'has_hull':hulls,'by_size':by_size,
            'scope':'closure-clause equisatisfiability for individual finite E/R pairs; not FC15 models'}

def equality_checks():
    counts=[]
    for n in (1,2,3):
        good=0
        for bits in range(1<<(n*n)):
            def e(x,y):return bool(bits&(1<<(n*x+y)))
            refl=all(e(x,x) for x in range(n))
            le=all(not(e(x,y) and e(x,z)) or e(y,z)
                   for x,y,z in product(range(n),repeat=3))
            sym=all(e(x,y)==e(y,x) for x,y in product(range(n),repeat=2))
            trans=all(not(e(x,y) and e(y,z)) or e(x,z)
                      for x,y,z in product(range(n),repeat=3))
            require((refl and le)==(refl and sym and trans),'equivalence basis')
            good+=refl and le
        counts.append({'n':n,'equivalence_relations':good})
    # Function congruence is indispensable even when source equalities are few.
    a,b=0,3
    fa,fb=K.construct(0,(a,0)),K.construct(0,(b,0))
    def l(pred,x,y,sign=True):return (1 if sign else -1)*(K.atom_code(pred,x,y)+1)
    toy=[(l('Eq',a,b),),(l('Eq',0,0),),(l('Inc',fa,0),),(-l('Inc',fb,0),),
         (-l('Eq',a,b),-l('Eq',0,0),l('Eq',fa,fb)),
         (-l('Eq',fa,fb),-l('Eq',0,0),-l('Inc',fa,0),l('Inc',fb,0))]
    require(K.solve(toy) is None,'missing equality transport')
    require(K.solve(toy[:4]+toy[5:]) is not None,'function congruence deletion control')
    return {'finite_equivalence_basis':counts,'equality_transport_unsat':True,
            'deleted_function_congruence_sat':True}

def codec_checks():
    rng=random.Random(1729)
    comparisons=roundtrips=rejects=0
    for ext,derived in product((False,True),repeat=2):
        values=list(range(10000))+[rng.getrandbits(256) for _ in range(1000)]
        for n in values:
            roundtrips+=1
            require(K.encode(K.decode(n,ext,derived),ext,derived)==n,'term codec round trip')
            if n:
                tag,payload=(n-1)%16,(n-1)//16
                fs=K.signature(ext,derived)
                arity=fs[tag][1] if tag<len(fs) else 1
                require(all(x<n for x in K.tuple_decode(payload,arity)),'descending children')
        fs=K.signature(ext,derived)
        cs=K.source_clauses(ext,derived)+K.equality_clauses(ext,fs)
        bits=K.payload_bits(cs,ext,fs)
        decoded=K.unpack_payload(bits,ext,derived)
        require(K.payload_bits(decoded,ext,fs)==bits,'template round trip')
        for original,roundtripped in zip(cs,decoded):
            ov=K.clause_variables(original);rv=K.clause_variables(roundtripped)
            require(len(ov)==len(rv),'template variable count')
            for values in product(range(2),repeat=len(ov)):
                comparisons+=1
                require(K.ground_clause(original,dict(zip(ov,values)),ext,derived)==
                        K.ground_clause(roundtripped,dict(zip(rv,values)),ext,derived),'template semantics')
        # Every 4-bit term opcode is used in the nine-function format.
        bad_inputs=[bits[:-1],bits+'0']
        if (6+len(fs)).bit_length()==5:
            bad_inputs.append('001100'+'11111'+bits[11:])
        for bad in bad_inputs:
            try:K.unpack_payload(bad,ext,derived)
            except ValueError:rejects+=1
            else:raise RuntimeError('malformed template accepted')
    return {'natural_term_roundtrips':roundtrips,'max_random_bits':256,
            'template_ground_comparisons':comparisons,'malformed_template_rejections':rejects}

def solver_checks():
    # All signed clauses over three atoms, all ordered pairs of such clauses,
    # and 5000 seeded random CNFs with three to eleven clauses.
    literals=(-3,-2,-1,1,2,3)
    clauses=[tuple(literals[i] for i in range(6) if mask&(1<<i)) for mask in range(64)]
    rng=random.Random(20261017)
    suite=[[]]+[[c] for c in clauses]+[[c,d] for c in clauses for d in clauses]
    suite += [[rng.choice(clauses) for _ in range(rng.randrange(3,12))] for _ in range(5000)]
    for cnf in suite:
        answer=K.solve(cnf)
        brute=K.exhaustive_sat(cnf)
        require((answer is None)==(brute is None),'solver disagreement')
        if answer is not None:require(K.valuation_satisfies(cnf,answer),'invalid SAT assignment')
    return {'cnfs_compared_with_exhaustive_truth_tables':len(suite)}

def main():
    t=time.monotonic()
    results={'codec':codec_checks(),'equality':equality_checks(),'solver':solver_checks(),
             'closure':finite_closure_checks()}
    results['elapsed_seconds']=round(time.monotonic()-t,3)
    results['all_passed']=True
    results['limitations']='Finite evidence only; ordinary proofs are in the report; no Lean/Coq certification or binary compilation.'
    path=Path(__file__).resolve().parents[1]/'data'/'validation.json'
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__':main()
