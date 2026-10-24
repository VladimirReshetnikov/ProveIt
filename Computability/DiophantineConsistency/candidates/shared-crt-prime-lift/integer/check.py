#!/usr/bin/env python3
"""Independent exact guard/whole-quartic/static-gate audit; imports no builder."""
from collections import defaultdict
import hashlib,json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent


def need(ok,text):
    if not ok:raise RuntimeError(text)


def sha(raw):return hashlib.sha256(raw).hexdigest()


def main():
    parent_path=HERE.parent/'affine/equation.json'
    parent_raw=parent_path.read_bytes()
    need(sha(parent_raw)=='e851ff1d420a39be069e63f6f117557356c38e6d8272a481258fe38cb38dc6ea','frozen actual natural parent')
    parent=json.loads(parent_raw);equation=json.loads((HERE/'equation.json').read_text())
    poly=json.loads((HERE/'expanded_polynomial.json').read_text())
    oldn=len(parent['variables']);oldrows=parent['residuals']
    need(equation['domain']=='unrestricted integers'and equation['variables'][:oldn]==parent['variables']and
         equation['residuals'][:len(oldrows)]==oldrows,'exact original variable/row prefix')
    semantics={i for i,v in enumerate(parent['variables'])if v['kind']in['outer','witness']}
    gates={i for i,v in enumerate(parent['variables'])if v['kind']=='gate'}
    need(len(semantics)==1670 and len(gates)==1939 and semantics|gates==set(range(oldn)),'semantic/gate partition')
    covered=set()
    for row in oldrows:
        if row['label']not in['addition','multiplication']:continue
        positives=[(c,m)for c,m in row['terms']if c>0]
        need(len(positives)==1 and positives[0][0]==1 and len(positives[0][1])==1,'monic gate output')
        i=positives[0][1][0]
        need(i in gates and i not in covered,'one definition per gate')
        for c,m in row['terms']:
            if m==[i]:continue
            need(c<0 and all(j<i for j in m),'nonnegative topological gate restoration')
        covered.add(i)
    need(covered==gates,'every unguarded gate forced nonnegative by induction')
    guards=equation['semantic_input_guards'];newrows=equation['residuals'][len(oldrows):]
    need(len(guards)==len(newrows)==1670 and {g['input']for g in guards}==semantics,'exact semantic coverage')
    auxiliary=set()
    for g,row in zip(guards,newrows):
        i=g['input'];a,b,c=g['auxiliaries']
        need(len({a,b,c})==3 and not({a,b,c}&auxiliary)and min(a,b,c)>=oldn,'fresh distinct guard coordinates')
        auxiliary|={a,b,c}
        actual={tuple(m):v for v,m in row['terms']}
        need(actual=={(i,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1},'exact three-square guard')
    need(auxiliary==set(range(oldn,8619))and len(equation['variables'])==8619,'full8619dimension')
    expanded=defaultdict(int);used=set()
    for row in equation['residuals']:
        need(len({tuple(m)for c,m in row['terms']})==len(row['terms']),'canonical residual support')
        for c,m in row['terms']:
            need(type(c)is int and c and m==sorted(m)and len(m)<=2 and all(type(i)is int and 0<=i<8619 for i in m),'literal quadratic monomial')
            used.update(m)
        for a,ma in row['terms']:
            for b,mb in row['terms']:
                expanded[tuple(sorted(ma+mb))]+=a*b
    wanted={m:c for m,c in expanded.items()if c};actual={tuple(m):c for c,m in poly['terms']}
    need(actual==wanted and len(actual)==len(poly['terms']),'complete collected quartic equals squared residuals')
    need(used==set(range(8619))and len(actual)==39811 and max(map(len,actual))==4 and max(map(abs,actual.values()))==127285349,'exact metrics/all variables live')
    need(actual[(8618,)*4]==1,'fresh auxiliary exact degree4 coefficient')
    represented={a*a+b*b+c*(c+1)for a in range(33)for b in range(33)for c in range(33)}
    need(all(n in represented for n in range(1001)),'bounded three-square completeness controls')
    receipt=dict(status='PASS',python_optimization=sys.flags.optimize,
                 natural_parent_sha256=sha(parent_raw),integer_equation_sha256=sha((HERE/'equation.json').read_bytes()),
                 integer_polynomial_sha256=sha((HERE/'expanded_polynomial.json').read_bytes()),
                 variables=8619,semantic_inputs_guarded=1670,fresh_auxiliaries=5010,
                 nonnegative_topological_gate_definitions=1939,quadratic_rows=len(equation['residuals']),
                 exact_degree=4,quartic_terms=39811,coefficient_height=127285349,
                 final_auxiliary_fourth_power_coefficient=1,all_variables_live=True,
                 bounded_three_square_completeness_cases=1001,
                 scope='Exact frozen prefix, guard additions, static nonnegative gate induction and full quartic expansion. Universal representation by Legendre theorem in README; no Lean/internal-ZFC derivation.')
    target=HERE/('CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json')
    target.write_text(json.dumps(receipt,indent=2)+'\n')
    print('PASS8619integerquartic,1670guards,1939positivegateinductions and all39811coefficients')


if __name__=='__main__':main()
