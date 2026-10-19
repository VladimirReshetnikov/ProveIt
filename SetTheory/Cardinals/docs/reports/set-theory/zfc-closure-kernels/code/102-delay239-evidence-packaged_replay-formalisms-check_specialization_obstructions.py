#!/usr/bin/env python3
"""Exact certificates for the logical-basis obstruction theorem.

Standard-library, proof-search-free, and independent of the emitted programs.
The universal term-family conclusion follows by induction from the checked
unique failing tuple and closed positive subalgebra; it is not a bounded term
search. This checks the logical rows, GEN, atomic fresh vacuity, and IR only.
Neither CP nor GIC is asserted valid in these interpretations.
"""
from __future__ import annotations
from itertools import product
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent
M3=[[2,2,2],[1,2,2],[0,1,2]]
M4=[[3,3,3,3],[1,3,3,3],[3,3,3,3],[2,1,0,3]]


def verify(matrix,order,kind):
    n=len(matrix);top=n-1;values=range(n);rank={x:i for i,x in enumerate(order)}
    assert len(rank)==n and set(rank)==set(values)
    C=lambda a,b:matrix[a][b]
    N=lambda a:C(a,0)
    Q=lambda a,b:min((a,b),key=rank.__getitem__)
    E=lambda a,b:N(Q(N(a),N(b)))
    L=lambda a,b,c,u:C(C(C(c,u),a),C(C(a,c),C(b,c)))
    cases={}
    def check(name,domain,predicate):
        count=0
        for item in domain:
            assert predicate(*item),(kind,name,item)
            count+=1
        cases[name]=count
    pairs=list(product(values,repeat=2));triples=list(product(values,repeat=3))
    quads=list(product(values,repeat=4))
    check('modus_ponens',pairs,lambda a,b: a!=top or C(a,b)!=top or b==top)
    check('identity',[(a,) for a in values],lambda a:C(a,a)==top)
    check('K',pairs,lambda a,b:C(a,C(b,a))==top)
    check('ex_falso',[(a,) for a in values],lambda a:C(0,a)==top)
    check('double_negation_elimination',[(a,) for a in values],lambda a:C(N(N(a)),a)==top)
    check('quantifier_distribution_rho2',quads,
          lambda p0,q0,p1,q1:C(Q(C(p0,q0),C(p1,q1)),C(Q(p0,p1),Q(q0,q1)))==top)
    check('quantifier_commutation_rho4',quads,
          lambda a,b,c,d:Q(Q(a,b),Q(c,d))==Q(Q(a,c),Q(b,d)))
    # All_x P is independent of x, so Exists_x All_x P = NN(Q(p0,p1)).
    check('rho6_at_both_domain_points',pairs,
          lambda a,b: C(E(Q(a,b),Q(a,b)),a)==top and C(E(Q(a,b),Q(a,b)),b)==top)
    check('atomic_fresh_vacuity',[(a,) for a in values],lambda a:C(a,Q(a,a))==top)
    check('GEN',[(top,)],lambda a:Q(a,a)==top)
    # Every equality column is either (top,0), (0,top), or (top,top)
    # when the quantified label coincides syntactically with the other label.
    check('equality_existence_rho1',[(top,0),(0,top),(top,top)],lambda a,b:E(a,b)==top)
    domain=range(2)
    eq=lambda x,y:top if x==y else 0
    congruence_cases=0
    # All binary membership valuations on the 2-element individual domain.
    # This includes and strictly strengthens the irreflexive witness check.
    for cells in product(values,repeat=4):
        R=lambda x,y:cells[2*x+y]
        for a,b,c in product(domain,repeat=3):
            assert C(eq(c,a),C(eq(c,b),eq(a,b)))==top
            assert C(eq(c,a),C(R(c,b),R(a,b)))==top
            assert C(eq(a,b),C(R(c,a),R(c,b)))==top
            congruence_cases+=1
    cases['three_equality_rows_all_membership_tables']=congruence_cases
    assert N(0)==top
    cases['irreflexivity_for_diagonal_zero']=1
    failures=[list(t)+[L(*t)] for t in quads if L(*t)!=top]
    if kind=='positive_term_family':
        assert failures==[[1,2,1,0,1]]
        assert all(C(a,b) in (1,2) for a,b in product((1,2),repeat=2))
        check('composition_B',triples,lambda a,b,c:C(C(a,b),C(C(b,c),C(a,c)))==top)
        # The certificate is all possible values of a positive term at the
        # sole failing (a,b,c)=(1,2,1), not an enumeration of finitely many terms.
        assert all(L(1,2,1,u)==top for u in (1,2))
        specialization={'all_implication_terms_over_a_b_c_Truth':True,
                        'proof':'Unique bad tuple requires u=0; {1,2} is closed under C and contains a,b,c,Truth at that tuple.'}
    else:
        check('rho8_u_neg_b',triples,lambda a,b,c:L(a,b,c,N(b))==top)
        specialization={'u':'b -> F','all_instances_valid':True}
    # Atom P=R(v0,v1), R(0,1)=1, diagonal0, valuation(v0,v1)=(0,1).
    p=1;false=0
    peirce=C(C(C(p,false),p),p)
    assert peirce==1 and peirce!=top
    return {'matrix':matrix,'designated':[top],'falsity':0,'forall_min_order':order,
            'individual_domain':[0,1],'membership_witness':[[0,1],[0,0]],
            'checked_instances':cases,'full_rho8_failing_tuples':failures,
            'specialization':specialization,'Peirce_P1_Q0':peirce,
            'scope':'Logical rows rho1-rho7, specialized rho8, GEN, MP, fresh atomic vacuity, IR. CP and GIC excluded.'}


def main():
    report={'status':'PASS','certificates':[verify(M3,[0,1,2],'positive_term_family'),verify(M4,[0,2,1,3],'negated_b')],
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'new_ZFC_equiconsistency_or_TM_bound_claimed':False}
    (HERE/'specialization_obstructions.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':report['status'],'certificates':[{k:v[k] for k in ('matrix','forall_min_order','checked_instances','Peirce_P1_Q0')} for v in report['certificates']]},indent=2))
if __name__=='__main__':main()
