#!/usr/bin/env python3
"""Exact residual transformation of package64 Q41; pure Python arithmetic."""
import ast
import hashlib
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE/'upstream'
spec=importlib.util.spec_from_file_location('upstream_poly',ROOT/'polynomial_arithmetic.py')
mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)

def require(v,msg):
    if not v: raise ValueError(msg)

def substitute_text(text, replacements):
    class Sub(ast.NodeTransformer):
        def visit_Name(self,node):
            if node.id in replacements:
                return ast.parse(replacements[node.id], mode='eval').body
            return node
    return ast.unparse(ast.fix_missing_locations(Sub().visit(ast.parse(text,mode='eval'))))

def main():
    raw=(ROOT/'quartic41.json').read_bytes(); parent=json.loads(raw)
    removed={'P','X','N','C2','Delta','V','Baux'}
    variables=[v for v in parent['variables'] if v not in removed]
    alg=mod.Poly(parent['variables']+parent['fixed_numerals'])
    q='(beta*J+1)'; k='(eta+zeta)'; H='(4*a+3)'
    restorations={
      'P':f'{k}+E*(c-eta)', 'X':'2*u**2', 'N':f'{q}*(L+1)',
      'C2':'c**2', 'Delta':'a**2+4*a+3', 'V':'f*o-c', 'Baux':'I**2',
      'tau':'tau+E*(c-eta)', 'D':'D+a*c'
    }
    deleted={1,6,9,10,15,19,22}
    rows=[]; identities=[]
    for i,expr in enumerate(parent['residuals']):
        changed=substitute_text(expr,restorations)
        poly=alg.parse(changed)
        if i in deleted:
            require(not poly,f'deleted source row {i} is nonzero')
            identities.append({'source_row':i,'image':'zero'})
            continue
        if i==17:
            # Old image = (fo-c)^2 + g-y^2. Add o^2(F2-f^2).
            changed='F2*o**2-2*f*o*c+c**2+g-y**2'
            candidate=alg.parse(changed)
            correction=alg.mul(alg.parse('o**2'),alg.parse('F2-f**2'))
            require(alg.add(candidate,poly,-1)==correction,'quotient-ring remainder identity')
            poly=candidate
            identities.append({'source_row':i,'child_row':len(rows),'correction':'o**2*(F2-f**2)'})
        else: identities.append({'source_row':i,'child_row':len(rows),'correction':'0'})
        rows.append(changed)
    nparent=len(parent['variables'])
    polynomials=[alg.parse(x) for x in rows]
    degrees=[max((sum(m[:nparent]) for m in p),default=0) for p in polynomials]
    require(len(variables)==34 and len(rows)==19,'dimension')
    require(max(degrees)==3,'cubic residual bound')
    sos={}
    for p in polynomials: sos=alg.add(sos,alg.mul(p,p))
    exponents=list(alg.zero)
    exponents[alg.index['I']]=4;exponents[alg.index['g']]=2
    require(sos.get(tuple(exponents))==1,'exact degree coefficient I^4*g^2')
    live={alg.variables[i] for p in polynomials for m in p for i,e in enumerate(m) if e}
    require(live==set(variables+parent['fixed_numerals']),'liveness')
    out=dict(name='sextic34_two_root_shears_and_square_remainder',domain='unrestricted integers',
      variables=variables,variable_count=34,fixed_numerals=parent['fixed_numerals'],
      residuals=rows,equation_count=19,residual_degrees=degrees,
      exact_degree=6,single_polynomial='sum of squares of the 19 listed residuals',
      aliases={'q':'beta*J+1','k':'eta+zeta','H':'4*a+3','C':'q-F-alpha'},
      parent_pin='9cca523d9f27ad39d52993f4065cbd7e58f8bdd4',
      parent_path='Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/integer41/quartic41.json',
      parent_sha256=hashlib.sha256(raw).hexdigest(),
      parent_restorations=restorations,
      transformations=identities,
      coefficient_binding=parent['coefficient_binding'],
      degree_certificate={'monomial':{'I':4,'g':2},'coefficient':1},
      proof_status='Exact integer zero-set bijection with pinned Q41, whose ordinary arithmetic/compiler calibration is inherited.')
    (HERE/'sextic34.json').write_text(json.dumps(out,indent=2)+'\n')
    receipt={'variable_count':34,'residual_count':19,'residual_degrees':degrees,
       'exact_degree':6,'expanded_terms_with_symbolic_ports':len(sos),
       'all_restoration_identities_checked':True,'remainder_correction_identity_checked':True,
       'all_variables_and_ports_live':True,'degree_certificate':out['degree_certificate']}
    (HERE/'SEXTIC34_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
