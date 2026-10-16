"""Finite logical counterinterpretations and equality-aware PSC alpha checks.

These are executable diagnostics, not first-order membership models, a Lean
proof, or an assertion about the actual C/G theory. Run without -O.
"""
from __future__ import annotations
import argparse
from itertools import product
import json
from pathlib import Path
import psc_adapter_checks as a


def rename_free(p, mapping, bound=frozenset()):
    if p[0] in ('m','q'):
        return (p[0], *(v if v in bound else mapping.get(v,v) for v in p[1:]))
    if p[0] in ('a','e'):
        return p[0],p[1],rename_free(p[2],mapping,bound|{p[1]})
    if p[0] in ('i','o','j'):
        return p[0],rename_free(p[1],mapping,bound),rename_free(p[2],mapping,bound)
    return p


def alpha(p, env=()):
    var=lambda i: ('bound',env.index(i)) if i in env else ('free',i)
    if p[0] in ('m','q'): return p[0],var(p[1]),var(p[2])
    if p[0] in ('a','e'): return p[0],alpha(p[2],(p[1],)+env)
    if p[0] in ('i','o','j'): return p[0],alpha(p[1],env),alpha(p[2],env)
    return p


def eq_alpha_checks():
    count=0
    for c in (2,3,4,5):
        atoms=[a.B]+[(tag,i,j) for tag in ('m','q') for i in range(c) for j in range(c)]
        forms=atoms+[q(i,p) for i in range(c) for p in atoms for q in (a.A,a.E)]
        forms += [q(p,r) for p in atoms for r in atoms for q in (a.I,a.O,a.J)]
        forms += [a.A(0,a.E(1,a.I(p,a.A(0,r)))) for p in atoms for r in atoms]
        for p in forms:
            x,y,z,bound,seed,hull=range(c+1,c+7)
            matrix=rename_free(p,{0:x,1:y})
            sb=a.A(x,a.E(bound,a.A(y,a.I(matrix,a.S(y,bound,z)))))
            guard=a.O(a.S(x,seed,z),a.M(x,hull))
            closed=a.A(x,a.I(guard,a.A(y,a.I(matrix,a.M(y,hull)))))
            support=a.A(y,a.I(a.M(y,hull),a.E(x,matrix)))
            reference=a.I(sb,a.A(seed,a.E(hull,a.J(closed,support))))
            assert alpha(a.fixed(p,c+2))==alpha(reference)
            count+=1
    return count


def modal_checks():
    """All truth subsets on a reflexive symmetric nontransitive3-world path."""
    full=7
    imp=lambda p,q: ((~p)|q)&full
    neg=lambda p:p^full
    access=((0,1),(0,1,2),(1,2))
    def box(i,p):
        if i: return p
        return sum(int(all(p>>v&1 for v in access[w]))<<w for w in range(3))
    ex=lambda i,p:neg(box(i,neg(p)))
    counts=dict(QI=0,UI_same=0,old_rho6=0,commutation=0,ax467=0)
    for i,p in product(range(2),range(8)):
        assert imp(box(i,p),p)==full;counts['UI_same']+=1
        assert imp(ex(i,box(i,p)),p)==full;counts['old_rho6']+=1
        for q in range(8):
            assert imp(box(i,imp(p,q)),imp(box(i,p),box(i,q)))==full
            counts['QI']+=1
        for j in range(2):
            assert imp(box(i,box(j,p)),box(j,box(i,p)))==full
            counts['commutation']+=1
            root=imp(imp(box(i,box(j,neg(box(i,box(j,p))))),box(i,p)),p)
            assert root==full;counts['ax467']+=1
    p=3  # true at0,1;false at2.
    introspection=imp(box(0,p),box(0,box(0,p)))
    protected=imp(box(0,imp(box(0,p),box(0,p))),imp(box(0,p),box(0,box(0,p))))
    assert not introspection&1 and not protected&1
    # Rel00=p; every other atom=false. Atomic fresh-name vacuity holds.
    for i,j,k in product(range(3),repeat=3):
        if k not in (i,j):
            atom=p if (i,j)==(0,0) else 0
            assert imp(atom,box(k,atom))==full
    return dict(valid_rows=counts, positive_introspection_false_at_world0=True,
                protected_QI_false_at_world0=True, atomic_fresh_vacuity_valid=True)


def check():
    if not __debug__: raise RuntimeError('run without -O: audit requires assertions')
    # With all quantifiers identity, every modal-only FOL quantifier axiom
    # valid on nonempty domains holds, but different atoms remain unrelated.
    rel00,rel11=True,False
    assert not ((not rel00) or rel11)
    return dict(equality_aware_alpha_cases=eq_alpha_checks(),modal=modal_checks(),
        identity_quantifiers_cross_variable_UI_fails=True,
        dead_quantifier_actual_bundle_control=a.check(),
        claims_complete_new_engine=False)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    text=json.dumps(check(),indent=2,sort_keys=True)+'\n'
    if args.output: args.output.write_text(text)
    print(text,end='')
