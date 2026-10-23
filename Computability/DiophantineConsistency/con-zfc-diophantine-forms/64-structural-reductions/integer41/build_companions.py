#!/usr/bin/env python3
"""Exact register elimination: 36 integer sextic and 31 integer octic."""
import ast
import json
from build_verify44 import ROOT, Poly, require, digest, write_json

def substitute(text, replacements):
    class Replace(ast.NodeTransformer):
        def visit_Name(self,node):
            if node.id in replacements:
                return ast.parse(replacements[node.id],mode='eval').body
            return node
    return ast.unparse(ast.fix_missing_locations(Replace().visit(ast.parse(text,mode='eval'))))

def build_one(name, source, substitutions, removed_rows, expected_n, expected_degree, certificate):
    variables=[x for x in source['variables'] if x not in substitutions]
    require(len(variables)==expected_n,'variable count '+name)
    algebra=Poly(variables+source['fixed_numerals'])
    residuals=[]
    for i,row in enumerate(source['residuals']):
        changed=substitute(row,substitutions)
        parsed=algebra.parse(changed)
        if i in removed_rows:
            require(parsed=={},'eliminated definition is exactly zero: '+str(i))
        else:
            residuals.append(changed)
    rows=[algebra.parse(row) for row in residuals]
    n=len(variables)
    deg=[max(sum(k[:n]) for k in row) for row in rows]
    require(max(deg)*2==expected_degree,'upper degree')
    sos={}
    for row in rows: sos=algebra.add(sos,algebra.mul(row,row))
    require(max(sum(k[:n]) for k in sos)==expected_degree,'exact degree')
    exponents=list(algebra.zero)
    for variable,power in certificate.items(): exponents[algebra.index[variable]]=power
    require(sos.get(tuple(exponents),0)==1,'unit leading coefficient')
    live={variables[i] for row in rows for k in row for i in range(n) if k[i]}
    require(live==set(variables),'all variables live')
    out=dict(name=name,domain='unrestricted integers',variables=variables,variable_count=n,
        fixed_numerals=source['fixed_numerals'],coefficient_binding=source['coefficient_binding'],
        residuals=residuals,equation_count=len(rows),residual_degrees=deg,
        single_polynomial='sum of squares of the listed residuals',exact_degree=expected_degree,
        elimination_definitions=substitutions,deleted_source_row_indices_zero_based=sorted(removed_rows),
        source='quartic41.json',source_sha256=digest((ROOT/'quartic41.json').read_bytes()),
        proof='COMPANIONS_PROOF.md',degree_certificate=dict(monomial=certificate,coefficient=1))
    write_json(ROOT/(name+'.json'),out)
    checks=dict(variables=n,equations=len(rows),residual_degrees=deg,
        exact_degree=expected_degree,degree_certificate=out['degree_certificate'],
        all_eliminated_definition_rows_vanish_identically=True,all_variables_live=True,
        expanded_monomials_with_symbolic_ports=len(sos))
    write_json(ROOT/'certificates'/(name.upper()+'_CHECKS.json'),checks)
    return checks

def main():
    source=json.loads((ROOT/'quartic41.json').read_text())
    q='(beta*J+1)'
    sextic=dict(N=q+'*(L+1)',X='4*w_scale*'+q,C2='c**2',F2='f**2',Baux='I**2')
    octic=dict(N=q+'**3',L=q+'**2-1',X='4*w_scale*'+q,C2='c**2',F2='f**2',
        Baux='I**2',g='y**2-V**2',P='E*(c-eta)+eta+zeta',
        D='4*w_scale*'+q+'+a*c+gamma*(4*a+3)',Delta='a**2+4*a+3')
    first=build_one('sextic36',source,sextic,{1,2,10,14,19},36,6,{'I':4,'g':2})
    second=build_one('octic31',source,octic,{0,1,2,6,8,9,10,14,17,19},31,8,{'I':4,'V':4})
    print(json.dumps(dict(sextic36=first,octic31=second),indent=2))

if __name__=='__main__': main()
