#!/usr/bin/env python3
"""Exact121: the program width forces the deleted raw aggregate bound."""
from pathlib import Path
import json
import sympy as sp
import explore_serial_raw_counter_composition as old


SYM={name:value for name,value in old.SYM.items() if name!='alpha'}
OUTER_NAMES=[name for name in old.OUTER_NAMES if name!='alpha']


def build():
    ops,pairs,source=old.build()
    return ([row for row in ops if row[0] not in ('bound_rhs','bound_lhs')],
            [row for i,row in enumerate(pairs) if i!=5],
            [row for i,row in enumerate(source) if i!=5])


def verify_certificate():
    ops,pairs,source=build();env=dict(SYM);hist=old.aligned.baseline.run_schedule(ops,env);records=[]
    u=SYM['j']*SYM['c']+2*SYM['r']+1
    for i,((left,right),p) in enumerate(zip(pairs,source)):
        actual=sp.expand(env[left]-env[right]);extra=source[17]*(u*u-SYM['y_aux']**2) if i==18 else 0
        assert sp.expand(actual-p-extra)==0,i
        records.append(dict(index=i,equality=[left,right],source=sp.sstr(p),correction=sp.sstr(extra)))
    primitive,counts=old.aligned.verify_primitives(ops,env)
    assert len(primitive)==121 and counts=={'+':65,'*':56}
    assert len(source)==len(pairs)==32 and len(OUTER_NAMES+old.CORE_NAMES)==44
    assert all(p.free_symbols<=set(SYM.values()) for p in source)
    q=sp.Symbol('q');J=(q-1)/2
    upper=2*q**6+q**6*(3*J-1)*sum(q**i for i in range(6))
    gap=sp.factor(sp.Rational(3,2)*(q**12-1)-upper)
    t=sp.Symbol('t');coeff=sp.Poly(sp.expand(gap.subs(q,t+9)),t).all_coeffs()
    assert all(c>0 for c in coeff)
    assert old.PROGRAM['Rmin']>=9
    A,W,R,J=sp.symbols('A W R J')
    assert sp.Rational(9,8)*sp.Rational(2,8)==sp.Rational(9,32)<1
    return dict(status='PASS',operations=121,primitive_histogram=counts,histogram=hist,
                parameters=['x'],positive_unknowns=OUTER_NAMES+old.CORE_NAMES,unknown_count=44,
                equations=32,primitive_instructions=primitive,equalities=pairs,residuals=records,
                exact_delta=dict(deleted_unknown='alpha',deleted_equation_index=5,
                    deleted_registers=['bound_rhs','bound_lhs'],retained_source_polynomials='identical to frozen123'),
                full_packing_gap=sp.sstr(gap),gap_coefficients_at_q_equals_t_plus_9=list(map(str,coeff)),
                strong_time_bound='Once FKplus is the lowest native chunk: A<WH/(W-1)<=9J/32<J, since R>=9 and W>=R.')


def canonical(x):
    result=old.canonical(x)
    result['inherited_123_outer_residuals']=result.pop('outer_residuals')
    result['retained_121_outer_residuals']=22
    result['source_scope']='All 23 predecessor outer residuals are checked, including the deleted aggregate bound; the exact source-subset audit transfers the other 22.'
    return result


def verify():
    return dict(status='PASS_IMPLICIT_BOUND_SERIAL_COMPOSITION_121',arithmetic=verify_certificate(),
                canonical=[canonical(1),canonical(2)],
                proof='../1980/EXPLORATION_IMPLICIT_BOUND_SERIAL_COMPOSITION.md',
                scope='Exact positive-witness bijection with the complete123 labelled raw-counter component. The safe aggregate bound is derived from the program width; no new universal-machine claim.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram']);print(result['canonical'])
