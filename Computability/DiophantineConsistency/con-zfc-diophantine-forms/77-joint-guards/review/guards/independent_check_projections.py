#!/usr/bin/env python3
"""Exact structural audit of higher-degree projections without expanding them.

Checks trusted compact base by full expansion, all restorations by a separate
sparse ring, all surviving formulas by literal AST substitution, monic inverse
steps, and exact top homogeneous coefficient certificates. No point sampling.
"""
import ast
import copy
import hashlib
import json
from pathlib import Path
from independent_check import (HERE, G, need, parse, add, neg, mul, power, const,
                               substitute, symbols, pure_coefficient)

J = G.parent/'joint'
REGISTERS = {
    'q':'beta*(3*J3+1)+1', 'W':'4*(3*w3+1)', 'X':'q*W',
    'Y':'(2*v_scale+1)*q**3', 'C':'q-F-alpha', 'k':'1-V+j*c+h*E',
    'H':'4*a+3', 'Delta':'a**2+4*a+3',
    'R':'((q-1)*(q-F)+alpha)*(q**2-1)+(MC+q*MF)*(3*J3+1)',
    'det':'(cone_A*F)*(cone_B*C)-(q-cone_A*F-cone_B*C)**2',
    'T':'eta*(k-eta)', 'pos':'1+pair_pos1**2+pair_pos2**2+pair_pos3*(pair_pos3+1)',
}
ROWS = [
    'a-E-Y', 'E-X*(a-E)', 'c-eta-k*(a-E)',
    'tau**2-E*(c-eta)*(k+E*(c-eta))-1',
    '(X+a*c+gamma*H)**2-Delta*c**2-1', 'c*j-V-R',
    '(K0+W)*C-F-z*(q-1)', 'V+c-f*o', 'I-(2*r+1)*c**2',
    'I**2-Delta*(f**2-1)', 'I**2*(V**2-y**2)+y**2-1',
    'det*T-(pair_root**2-det-T+1)**2-pos',
]


def tree(text):
    return ast.parse(text,mode='eval').body


def replace_tree(node,mapping):
    """Simultaneous substitution, not recursive substitution into replacements."""
    if isinstance(node,ast.Name) and node.id in mapping:
        return copy.deepcopy(mapping[node.id])
    node = copy.deepcopy(node)
    for field,value in ast.iter_fields(node):
        if isinstance(value,ast.AST):
            setattr(node,field,replace_tree(value,mapping))
        elif isinstance(value,list):
            setattr(node,field,[replace_tree(v,mapping) if isinstance(v,ast.AST) else v for v in value])
    return node


def canonical(node):
    return ast.dump(node,include_attributes=False)


def text_of(node):
    return ast.unparse(node)


def expanded_registers():
    done = {}
    for name,expression in REGISTERS.items():
        done[name] = replace_tree(tree(expression),done)
    return done


def top(node,variables):
    """An AST upper degree bound and its exact homogeneous part at that bound."""
    if isinstance(node,ast.Constant):
        need(type(node.value) is int,'only integer coefficients')
        return 0,const(node.value)
    if isinstance(node,ast.Name):
        return (1 if node.id in variables else 0), {(node.id,):1}
    if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):
        d,p=top(node.operand,variables)
        return d,neg(p)
    need(isinstance(node,ast.BinOp),'polynomial arithmetic only')
    if isinstance(node.op,ast.Pow):
        need(isinstance(node.right,ast.Constant) and type(node.right.value) is int and node.right.value>=0,
             'nonnegative literal exponent')
        d,p=top(node.left,variables)
        return d*node.right.value,power(p,node.right.value)
    da,a=top(node.left,variables); db,b=top(node.right,variables)
    if isinstance(node.op,ast.Mult):
        return da+db,mul(a,b)
    need(isinstance(node.op,(ast.Add,ast.Sub)),'only polynomial ring operations')
    if isinstance(node.op,ast.Sub):
        b=neg(b)
    d=max(da,db)
    return d,add(a if da==d else {},b if db==d else {})


def main():
    basepath=J/'joint24_degree12.json'
    base=json.loads(basepath.read_text())
    expanded=expanded_registers()
    base_trees=[replace_tree(tree(e),expanded) for e in ROWS]
    base_polys=[parse(text_of(e)) for e in base_trees]
    need(base_polys==list(map(parse,base['residuals'])),'independently written compact base equals every expanded parent row')
    # Each inverse step names its monic row, variable, and already-expanded polynomial.
    # Expressions may use the fixed explanatory base registers; earlier inverses
    # are simultaneously propagated before checking the next step.
    forms = [
        ('joint23_degree12_eliminate_I',[(8,'I','(2*r+1)*c**2')],True),
        ('joint21_degree20',[(7,'V','f*o-c'),(8,'I','(2*r+1)*c**2'),(0,'a','E+Y')],False),
        ('joint20_degree32',[(7,'V','f*o-c'),(8,'I','(2*r+1)*c**2'),(0,'E','a-Y'),(1,'a','(X+1)*Y')],False),
        ('joint19_degree88',[(7,'V','f*o-c'),(8,'I','(2*r+1)*c**2'),(0,'E','a-Y'),(1,'a','(X+1)*Y'),(2,'eta','c-Y*k')],False),
    ]
    receipts=[]
    for name,steps,reduced in forms:
        file=J/(name+'.json')
        need(file.exists(),name+' required final projection packet exists')
        data=json.loads(file.read_text())
        need(data['parent_sha256']==hashlib.sha256(basepath.read_bytes()).hexdigest(),name+' exact parent pin')
        need(data['coefficient_binding']==base['coefficient_binding'] and data['fixed_numerals']==base['fixed_numerals'],
             name+' unchanged actual numeral binding')
        restore={}
        for row_index,variable,formula in steps:
            expr=parse(text_of(replace_tree(tree(formula),expanded)))
            expr=substitute(expr,restore)
            current=substitute(base_polys[row_index],restore)
            wanted=add(parse(variable),neg(expr))
            need(current==wanted or current==neg(wanted),name+' verified monic inverse for '+variable)
            # Propagate new inverse into all previously solved coordinates.
            restore={v:substitute(p,{variable:expr}) for v,p in restore.items()}
            restore[variable]=expr
        advertised={n:parse(e) for n,e in data['full_parent_restoration'].items()}
        need(advertised==restore,name+' exact complete polynomial restoration')
        need(set().union(*(symbols(p) for p in restore.values())) <= set(data['variables']+data['fixed_numerals']),
             name+' restorations use retained integer inputs only')
        need(data['variables']==[v for v in base['variables'] if v not in restore],name+' exact quantifier deletion')
        need(data['variable_count']==len(data['variables']),name+' variable count')
        target_rows=list(base_trees)
        if reduced:
            reduced_tree=replace_tree(tree('Delta*(f**2-1)*(V**2-y**2)+y**2-1'),expanded)
            need(add(base_polys[10],neg(parse(text_of(reduced_tree))))==mul(parse('V**2-y**2'),base_polys[9]),
                 name+' reversible auxiliary reduction, strong row retained')
            target_rows[10]=reduced_tree
        # Literal substitution using advertised expanded ASTs is now trustworthy
        # because their polynomial meanings were independently verified above.
        ast_restore={n:tree(e) for n,e in data['full_parent_restoration'].items()}
        deleted=sorted(i for i,_,_ in steps)
        need(data['deleted_parent_rows_zero_based']==deleted,name+' exact deleted row list')
        for i in deleted:
            need(not substitute(base_polys[i],restore),name+' deleted row is identically zero')
        expected=[replace_tree(e,ast_restore) for i,e in enumerate(target_rows) if i not in deleted]
        actual=list(map(tree,data['residuals']))
        need(len(actual)==data['residual_count']==len(expected),name+' exact row count')
        need([canonical(t) for t in actual]==[canonical(t) for t in expected],
             name+' every delivered factored residual is the exact structural substitution')
        live={n.id for t in actual for n in ast.walk(t) if isinstance(n,ast.Name)}
        variables=set(data['variables'])
        need(live==variables|set(data['fixed_numerals']),name+' no hidden register or dead unknown')
        tops=[top(t,variables) for t in actual]
        half=data['exact_degree']//2
        need(all(d<=half for d,_ in tops),name+' universal total-degree upper bound')
        highest={}
        for d,p in tops:
            if d==half:
                highest=add(highest,mul(p,p))
        witness=data['degree_witness']
        coeff=pure_coefficient(highest,witness['monomial'],variables)
        need(coeff==parse(witness['coefficient_expression']),name+' exact leading coefficient expression')
        need(coeff and all(c>0 and all(v=='beta' for v in m) for m,c in coeff.items()),
             name+' certificate strictly positive at authentic beta')
        receipts.append({'name':name,'variables':len(variables),'residuals':len(actual),
                         'degree_upper_bounds':[d for d,_ in tops], 'exact_SOS_degree':data['exact_degree'],
                         'degree_witness':witness,'monic_inverse_order':[v for _,v,_ in steps],
                         'auxiliary_reduced':reduced,'sha256':hashlib.sha256(file.read_bytes()).hexdigest()})
    need(receipts,'at least one projected family present')
    result={'status':'PASS','optimized_python':not __debug__,'packets':receipts,
            'implementation':'Independent AST structural substitution, exact sparse checks of parent and monic inverses, exact top-homogeneous coefficient arithmetic; no author imports or random tests',
            'scope':'Universal integer-polynomial projection and row-equivalence checks, not an independent proof of the inherited arithmetic/compiler endpoint. No expansion-support claim for the high-degree packets.'}
    (HERE/('PROJECTION_CHECKS_OPTIMIZED.json' if not __debug__ else 'PROJECTION_CHECKS.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
