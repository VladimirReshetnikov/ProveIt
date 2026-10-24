#!/usr/bin/env python3
"""Independent exact review of the shared binary DAG evaluators.

Uses only this reviewer's previously written sparse ring and compact parent.
No author circuit builder, verifier, or arithmetic implementation is imported.
"""
from pathlib import Path
from collections import Counter
import ast
import copy
import hashlib
import json
import sys

HERE=Path(__file__).resolve().parent
WAVE=HERE.parents[1]
CIRCUITS=WAVE/'circuits'
sys.path.insert(0,str(HERE.parent/'guards'))
from independent_check import need, parse, const, add, neg, mul, sos
from independent_check_projections import REGISTERS, ROWS

FAMILY=['joint19_degree88','joint20_degree32','joint21_degree20',
        'joint22_degree16','joint23_degree12','joint25_octic']
RESTORE={
    'joint19_degree88':{'V':'f*o-c','I':'(2*r+1)*c**2','E':'X*Y','a':'(X+1)*Y','eta':'c-Y*k'},
    'joint20_degree32':{'V':'f*o-c','I':'(2*r+1)*c**2','E':'X*Y','a':'(X+1)*Y'},
    'joint21_degree20':{'V':'f*o-c','I':'(2*r+1)*c**2','a':'E+Y'},
    'joint22_degree16':{'V':'f*o-c','I':'(2*r+1)*c**2'},
    'joint23_degree12':{'V':'f*o-c'},
    'joint25_octic':{},
}


def inline(expression,definitions):
    nodes={n:ast.parse(e,mode='eval').body for n,e in definitions.items()}
    def walk(node,stack=()):
        if isinstance(node,ast.Name) and node.id in nodes:
            need(node.id not in stack,'acyclic explanatory polynomial definitions')
            return walk(copy.deepcopy(nodes[node.id]),stack+(node.id,))
        node=copy.deepcopy(node)
        for field,value in ast.iter_fields(node):
            if isinstance(value,ast.AST):
                setattr(node,field,walk(value,stack))
            elif isinstance(value,list):
                setattr(node,field,[walk(v,stack) if isinstance(v,ast.AST) else v for v in value])
        return node
    return walk(ast.parse(expression,mode='eval').body)


def poly(node):
    return parse(ast.unparse(node))


def ancestors(rows,roots,cut=()):
    required=set(roots)
    cut=set(cut)
    for gate,operation,left,right in reversed(rows):
        if gate in required and gate not in cut:
            if isinstance(left,str):required.add(left)
            if isinstance(right,str):required.add(right)
    return required


def evaluate(rows,roots,seed):
    needed=ancestors(rows,roots,seed)
    values=dict(seed)
    for gate,operation,left,right in rows:
        if gate not in needed or gate in values:
            continue
        a=values[left] if isinstance(left,str) else const(left)
        b=values[right] if isinstance(right,str) else const(right)
        values[gate]=add(a,b) if operation=='+' else add(a,neg(b)) if operation=='-' else mul(a,b)
    return {r:values[r] for r in roots}


def references(name):
    definitions=dict(REGISTERS)
    definitions.update(RESTORE[name])
    rows=list(ROWS)
    omitted={i for v,i in [('V',7),('I',8),('a',0),('E',1),('eta',2)] if v in RESTORE[name]}
    if name=='joint22_degree16':
        rows[10]='Delta*(f**2-1)*(V**2-y**2)+y**2-1'
    indices=[i for i in range(11) if i not in omitted]
    selected=[rows[i] for i in indices]
    if name=='joint25_octic':
        definitions['T']='eta*zeta'
        selected.append('zeta-k+eta')
        indices.append('restore_zeta')
    selected.append(rows[11]);indices.append(11)
    return definitions,selected,indices


def check(name):
    file=CIRCUITS/(name+'_dag.json')
    packet=json.loads(file.read_text())
    sourcepath=(CIRCUITS/packet['source_polynomial']).resolve()
    need(sourcepath==(WAVE/'joint'/(name+'.json')).resolve(),name+' exact source destination')
    raw=sourcepath.read_bytes();source=json.loads(raw)
    need(hashlib.sha256(raw).hexdigest()==packet['source_sha256'],name+' pinned source identity')
    need(packet['witnesses']==source['variables'] and packet['fixed_numerals']==source['fixed_numerals'],
         name+' exact quantified variables and fixed leaves')
    need(packet['domain']==source['domain']=='unrestricted integers',name+' same integer domain')
    need(packet['coefficient_binding']==source['coefficient_binding'],name+' complete fixed tuple')
    need(packet['exact_degree']==source['exact_degree'],name+' correct inherited exact degree')
    rows=packet['source'];inputs=packet['witnesses']+packet['fixed_numerals']
    known=set(inputs);gates=[]
    need(len(known)==len(inputs),name+' distinct declared leaves')
    literals=set()
    for row in rows:
        need(type(row) is list and len(row)==4,name+' binary gate schema')
        gate,operation,left,right=row
        need(type(gate) is str and gate not in known and operation in ('+','-','*'),name+' unique valid gate')
        for operand in (left,right):
            need(type(operand) in (str,int),name+' only integer literals or references')
            if type(operand) is str:
                need(operand in known,name+' no forward or hidden reference')
            else:
                literals.add(operand)
        known.add(gate);gates.append(gate)
    roots=packet['residuals'];output=packet['output']
    need(output in gates and all(r in gates for r in roots),name+' output/residual gate references')
    need(len(set(roots))==len(roots),name+' separate residual roots')
    live=ancestors(rows,[output]);system_live=ancestors(rows,roots)
    need(set(gates)<=live and set(inputs)<=live,name+' every counted gate and input is live')
    operations=len(rows);system_operations=sum(g in system_live for g in gates)
    histogram=dict(Counter(row[1] for row in rows))
    need(operations==packet['operations'],name+' actual live binary gate count')
    need(system_operations==packet['system_operations'],name+' actual shared-system gate count')
    need(histogram==packet['operation_breakdown'],name+' exact multiplication/addition/subtraction histogram')
    need(operations-system_operations==2*len(roots)-1,name+' full finalizer counts every square and addition')
    definitions,expressions,indices=references(name)
    need(indices==packet['source_row_indices'] and len(expressions)==len(roots)==source['residual_count'],
         name+' exact literal residual order')
    expected=[inline(e,definitions) for e in expressions]
    if name in ('joint19_degree88','joint20_degree32','joint21_degree20'):
        actual=[ast.parse(e,mode='eval').body for e in source['residuals']]
        need([ast.dump(x,include_attributes=False) for x in actual]==
             [ast.dump(x,include_attributes=False) for x in expected],name+' exact fully inlined source binding')
        binding='literal AST after complete inline expansion'
    else:
        need([poly(e) for e in expected]==list(map(parse,source['residuals'])),name+' exact expanded source binding')
        binding='exact sparse polynomial equality'
    # Each cut is first proved as a polynomial in the ORIGINAL source inputs.
    cuts=['W','X','Y']
    cut_refs={n:packet['named_registers'][n] for n in cuts}
    need(len(set(cut_refs.values()))==len(cuts),name+' distinct cut references')
    atoms={v:{(v,):1} for v in inputs}
    actual_cuts=evaluate(rows,list(cut_refs.values()),atoms)
    for n in cuts:
        need(actual_cuts[cut_refs[n]]==poly(inline(REGISTERS[n],REGISTERS)),name+' universal cut definition '+n)
    # Equality over independent cut symbols implies equality after substituting
    # the now-validated actual cut values. No sample points are involved.
    cut_atoms=dict(atoms)
    cut_atoms.update({cut_refs[n]:{('cut_'+n,):1} for n in cuts})
    actual=evaluate(rows,roots,cut_atoms)
    partial={k:v for k,v in definitions.items() if k not in cuts}
    partial.update({n:'cut_'+n for n in cuts})
    term_counts=[]
    for i,(root,expression) in enumerate(zip(roots,expressions)):
        target=poly(inline(expression,partial))
        need(actual[root]==target,name+' exact staged residual '+str(i))
        term_counts.append(len(target))
    # Finalizer is separately checked with arbitrary independent residuals.
    residual_atoms={root:{('residual_'+str(i),):1} for i,root in enumerate(roots)}
    final=evaluate(rows,[output],residual_atoms)[output]
    need(final==sos(list(residual_atoms.values())),name+' exact unchanged final sum of squares')
    return {'name':name,'variables':len(packet['witnesses']),'exact_degree':packet['exact_degree'],
            'live_binary_operations':operations,'shared_residual_operations':system_operations,
            'final_SOS_operations':operations-system_operations,'operation_breakdown':histogram,
            'source_binding':binding,'exact_cut_definitions':cuts,'staged_residual_supports':term_counts,
            'integer_literal_leaves':sorted(literals),
            'dag_sha256':hashlib.sha256(file.read_bytes()).hexdigest(),'polynomial_sha256':packet['source_sha256'],
            'status':'PASS'}


def main():
    result={'status':'PASS','optimized_python':not __debug__,'packets':[check(name) for name in FAMILY],
            'count_convention':'All live binary +,-,* gates, including scalar products, squares, residual formation and final SOS. Fixed integer leaves and shared register reuse cost zero. Not bit complexity or a minimal-circuit claim.',
            'proof':'Exact source polynomial binding, universal original-input cut identities, exact residual identities over independent cuts, and universal final SOS identity. No numerical sampling.',
            'independence':'Imports only reviewer-owned sparse and compact-source code; no construction builder/checker/ring imported.'}
    (HERE/('CHECKS_OPTIMIZED.json' if not __debug__ else 'CHECKS.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
