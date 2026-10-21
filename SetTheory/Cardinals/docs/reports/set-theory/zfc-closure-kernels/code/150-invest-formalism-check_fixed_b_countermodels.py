#!/usr/bin/env python3
"""Replay two explicit four-value diagnostics without a SAT/SMT dependency.

B=C is checked against the full exact native calculus, including the literal
seed bundle. B=truth is checked only as a propositional basis with truth/alias/MP.
The finite checks support the ordinary unbounded proof in the accompanying note.
"""
from pathlib import Path
from itertools import product
import json,hashlib
import upstream_quantifier_checker as h

VALUES=range(4);T=0;F=1
PURE=((0,1,2,1),(0,0,2,0),(0,1,0,1),(2,2,2,2))
NATIVE=((0,3,3,3),(0,2,0,2),(3,3,0,3),(0,0,0,0))
QUANT=(0,3,3,3);EQ=1

def check_algebra(table,policy):
    I=lambda a,b:table[a][b]
    L=lambda a,b,c,u:I(I(I(c,u),a),I(I(a,c),I(b,c)))
    assert I(T,T)==T
    assert all(a!=T or I(a,b)!=T or b==T for a,b in product(VALUES,repeat=2))
    assert all(L(a,policy(c),c,u)==T for a,c,u in product(VALUES,repeat=3))
    Kbad=[(a,b)for a,b in product(VALUES,repeat=2)if I(a,I(b,a))!=T]
    Lbad=[(a,b,c,u)for a,b,c,u in product(VALUES,repeat=4)if L(a,b,c,u)!=T]
    assert Kbad and Lbad
    return {'I':table,'T':T,'designated':[T],'truth_alias':True,'MP':True,
            'restricted_instances':64,'K_failures':Kbad,'unrestricted_rho8_failures':Lbad}

def evaluate(form,env):
    tag,*xs=form
    if tag=='zero':return T
    if tag=='parameter':return env[xs[0]]
    if tag=='I':return NATIVE[evaluate(xs[0],env)][evaluate(xs[1],env)]
    if tag=='Q':return QUANT[evaluate(xs[1],env)]
    if tag=='R':return F
    if tag=='E':return EQ
    raise ValueError(tag)

def main():
    if not __debug__:raise RuntimeError('Assertions must be enabled; do not use python -O.')
    pure=check_algebra(PURE,lambda c:T)
    pure['scope']='Only rho8 with B=truth, truth zero, native truth alias, and MP; no retained quantifier/theory claim.'
    native=check_algebra(NATIVE,lambda c:c)
    assert QUANT[T]==T and F!=T
    I=lambda a,b:NATIVE[a][b]
    N=lambda a:I(a,F)
    Ex=lambda a:N(QUANT[N(a)])
    assert Ex(EQ)==T
    assert I(EQ,I(F,F))==T
    assert I(EQ,I(EQ,QUANT[EQ]))==T
    assert all(I(QUANT[I(a,b)],I(QUANT[a],QUANT[b]))==T for a,b in product(VALUES,repeat=2))
    assert all(I(QUANT[QUANT[a]],QUANT[QUANT[a]])==T for a in VALUES)
    assert all(I(Ex(QUANT[a]),a)==T for a in VALUES)
    # Independently interpret the retained repository's exact term constructors.
    a,b,c,m=map(h.P,('a','b','c','m'))
    rows={
        'rho1':h.Ex(a,h.E(a,b)),
        'rho2':h.I(h.Q(a,h.I(b,c)),h.I(h.Q(a,b),h.Q(a,c))),
        'rho3':h.I(h.E(a,b),h.I(h.R(c,a),h.R(c,b))),
        'rho4':h.I(h.Q(a,h.Q(b,c)),h.Q(b,h.Q(a,c))),
        'rho5':h.I(h.E(c,a),h.I(h.R(c,b),h.R(a,b))),
        'rho6':h.I(h.Ex(a,h.Q(a,b)),b),
        'G':h.I(h.E(c,a),h.I(h.E(c,b),h.Q(h.R(a,b),h.E(a,b)))),
        'bundle':h.N(h.I(h.I(h.R(a,b),h.Q(c,h.R(a,b))),h.nks(a,b,c))),
    }
    checked=0
    for va,vb,vc in product(VALUES,repeat=3):
        env={'a':va,'b':vb,'c':vc,'m':vc}
        for name,form in rows.items():
            assert evaluate(form,env)==T,(name,env);checked+=1
    native.update(Q=QUANT,R_constant=F,E_constant=EQ,F=F,GEN=True,
                  retained_row_AST_checks=checked,literal_bundle_for_all_matrix_values=True,
                  scope='Full native calculus with B=C restricted rho8, truth/alias, MP, GEN, rho1-rho6, G, literal original gated bundles; target1 has undesignated value1.')
    out={'status':'EXPLICIT_FOUR_VALUE_COUNTERMODELS_PASS','B_truth_propositional_only':pure,'B_C_full_native':native,
         'proof_scope':'Finite universal operation checks plus the ordinary native-code recursion/proof-induction argument in fixed_b_countermodels.md; not a proof-assistant theorem.'}
    raw=json.dumps(out,indent=2)+'\n'
    (Path(__file__).parent/'fixed_b_countermodels_receipt.json').write_text(raw)
    print(json.dumps({'status':out['status'],'B_C_retained_AST_checks':checked,'receipt_sha256':hashlib.sha256(raw.encode()).hexdigest()}))
if __name__=='__main__':main()
