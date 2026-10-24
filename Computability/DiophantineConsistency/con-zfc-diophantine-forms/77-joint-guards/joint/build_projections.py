#!/usr/bin/env python3
"""Emit entirely inlined, factored ordinary integer polynomials, without expansion."""
from pathlib import Path
import ast, copy, hashlib, json

ROOT=Path(__file__).resolve().parent

REGISTERS={
    'q':'beta*(3*J3+1)+1', 'W':'4*(3*w3+1)', 'X':'q*W',
    'Y':'(2*v_scale+1)*q**3','C':'q-F-alpha','k':'1-V+j*c+h*E',
    'H':'4*a+3','Delta':'a**2+4*a+3',
    'R':'((q-1)*(q-F)+alpha)*(q**2-1)+(MC+q*MF)*(3*J3+1)',
    'det':'(cone_A*F)*(cone_B*C)-(q-cone_A*F-cone_B*C)**2',
    'T':'eta*(k-eta)',
    'pos':'1+pair_pos1**2+pair_pos2**2+pair_pos3*(pair_pos3+1)',
}
ROWS=[
    'a-E-Y',
    'E-X*(a-E)',
    'c-eta-k*(a-E)',
    'tau**2-E*(c-eta)*(k+E*(c-eta))-1',
    '(X+a*c+gamma*H)**2-Delta*c**2-1',
    'c*j-V-R',
    '(K0+W)*C-F-z*(q-1)',
    'V+c-f*o',
    'I-(2*r+1)*c**2',
    'I**2-Delta*(f**2-1)',
    'I**2*(V**2-y**2)+y**2-1',
    'det*T-(pair_root**2-det-T+1)**2-pos',
]

def inline(expression, registers):
    parsed={n:ast.parse(e,mode='eval').body for n,e in registers.items()}
    def visit(n, stack=()):
        if isinstance(n,ast.Name) and n.id in parsed:
            if n.id in stack:raise ValueError('Cyclic definition '+n.id)
            return visit(copy.deepcopy(parsed[n.id]),stack+(n.id,))
        for field,value in ast.iter_fields(n):
            if isinstance(value,ast.AST):setattr(n,field,visit(value,stack))
            elif isinstance(value,list):setattr(n,field,[visit(v,stack) if isinstance(v,ast.AST) else v for v in value])
        return n
    return ast.unparse(visit(ast.parse(expression,mode='eval').body))

def main():
    base=json.loads((ROOT/'joint24_degree12.json').read_text())
    (ROOT/'COMPACT_BASE24.json').write_text(json.dumps({'registers':REGISTERS,'rows':ROWS,'fully_inlined_residuals':[inline(e,REGISTERS) for e in ROWS]},indent=2)+'\n')
    forms=[
        ('joint23_degree12_eliminate_I', {'I':'(2*r+1)*c**2'}, {8}, 12,'E**4*eta**4*h**4','1',True),
        ('joint21_degree20', {'V':'f*o-c','I':'(2*r+1)*c**2','a':'E+Y'}, {7,8,0},20,'f**4*v_scale**4*J3**12','2**4*3**12*beta**12',False),
        ('joint20_degree32', {'V':'f*o-c','I':'(2*r+1)*c**2','E':'X*Y','a':'(X+1)*Y'}, {7,8,0,1},32,'eta**4*h**4*w3**4*v_scale**4*J3**16','2**12*3**20*beta**16',False),
        ('joint19_degree88', {'V':'f*o-c','I':'(2*r+1)*c**2','E':'X*Y','eta':'c-Y*k','a':'(X+1)*Y'}, {7,8,0,2,1},88,'h**8*w3**8*v_scale**16*J3**56','2**32*3**64*beta**56',False),
    ]
    summary=[]
    for name,restored,deleted,degree,witness,coefficient,reduce_aux in forms:
        registers=dict(REGISTERS);registers.update(restored)
        row_formulas=list(ROWS)
        if reduce_aux:row_formulas[10]='Delta*(f**2-1)*(V**2-y**2)+y**2-1'
        residuals=[inline(e,registers) for i,e in enumerate(row_formulas) if i not in deleted]
        variables=[n for n in base['variables'] if n not in restored]
        live={n.id for e in residuals for n in ast.walk(ast.parse(e,mode='eval')) if isinstance(n,ast.Name)}
        if live!=set(variables+base['fixed_numerals']):raise ValueError('Unbound or dead symbol '+name)
        packet={k:base[k] for k in ('domain','fixed_numerals','coefficient_binding','single_equation','proof','proof_status')}
        packet.update(name=name,variables=variables,variable_count=len(variables),residuals=residuals,residual_count=len(residuals),exact_degree=degree,degree_witness={'monomial':witness,'coefficient_expression':coefficient,'positivity_reason':'beta=2^1064921-1>0'},parent='joint24_degree12.json',parent_sha256=hashlib.sha256((ROOT/'joint24_degree12.json').read_bytes()).hexdigest(),compact_registers=REGISTERS,compact_source_rows=ROWS,restoration_abbreviations=restored,full_parent_restoration={n:inline(e,registers) for n,e in restored.items()},deleted_parent_rows_zero_based=sorted(deleted),auxiliary_row_reduction=('aux_new = aux_old - (V**2-y**2)*strong; strong retained' if reduce_aux else 'none; retain original auxiliary row before substituting I and V'),residual_representation='Completely inlined, factored ordinary polynomials. compact_registers and restoration_abbreviations are explanatory and introduce no quantified coordinates.')
        (ROOT/(name+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
        summary.append({'name':name,'variables':len(variables),'rows':len(residuals),'degree':degree,'degree_witness':packet['degree_witness']})
    (ROOT/'PROJECTION_BUILD.json').write_text(json.dumps({'status':'EMITTED; run check_projections.py for independent exact validation','packets':summary},indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
