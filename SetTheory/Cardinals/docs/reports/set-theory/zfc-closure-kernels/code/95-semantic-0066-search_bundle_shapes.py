#!/usr/bin/env python3
"""Search all 11 ordered n-ary conjunction trees and 24 component orders.

All internal nodes are the minimal-logic negative conjunction
  And_F(a1,...,ak) = (a1 -> ... -> ak -> F) -> F.
Flattening and reassociation preserve this formula up to derivability in K,S.
No fourth-parameter deletion or helper-stack change occurs in this experiment.
"""
from functools import cache
import itertools
import json
from time import monotonic
import basis_experiment as b
import prepare_basis_routing as r
from search_flat_bundle import parts, flat

@cache
def trees(xs):
    if len(xs)==1:return (xs[0],)
    out=[]
    for mask in range(1,1<<(len(xs)-1)):
        cuts=[0]+[i+1 for i in range(len(xs)-1) if mask>>i&1]+[len(xs)]
        groups=[xs[a:c] for a,c in zip(cuts,cuts[1:])]
        out.extend(itertools.product(*(trees(g) for g in groups)))
    return tuple(out)

def formula(shape, order):
    if isinstance(shape,int):return parts[order[shape]]
    return flat([formula(t,order) for t in shape])

def display(shape,order):
    if isinstance(shape,int):return order[shape]
    return '('+','.join(display(t,order) for t in shape)+')'

def main():
    shapes=trees((0,1,2,3))
    assert len(shapes)==11 and len(set(shapes))==11
    best=None
    results=[]
    start=monotonic()
    for shape in shapes:
      for order in itertools.permutations('CGRE'):
        bundle=formula(shape,order)
        program=b.prefix+[m for row in b.old_rows for m in b.tb.emit(row)]+b.tb.emit(bundle)+b.tb.TAIL
        stack,_=b.tb.symbolic(program)
        assert stack==['old_top',b.spec['wal']('a','h')]+b.old_rows+[bundle]
        raw=''.join(b.macro_words[m] for m in program)
        candidates=[]
        for penalty in (0,.1,.4,1):
            try:
                chunks=r.segment(raw,penalty)
                root,rules,props=r.assemble(chunks)
            except ValueError:continue
            if props[1]<=6:candidates.append((len(rules),root,rules,props))
        if not candidates:continue
        nr,root,rules,props=min(candidates,key=lambda x:x[0])
        result=dict(shape=display(shape,order),AX_macro_count=len(program),
                    AX_min_dictionary_calls=len(b.spelling(raw)),
                    fine_operations=len(b.expansion(raw)),grammar_rules=nr,
                    estimated_working_states=117+nr,props=props,
                    exact_symbolic_AXIOM_stack=True)
        results.append(result)
        if best is None or nr<best['grammar_rules']:
            best=result.copy()
            best['bundle_ast']=bundle
            folder=r.write_inputs('bundle_shapes_best',root,rules,props)
            (folder/'basis_ast.json').write_text(json.dumps(dict(basis_ast=[b.old_rows[0]],bundle_ast=bundle,
                 helper_rows=8,retains_u=True,logical_status='Equivalent in minimal implication via negative-conjunction flattening',
                 shape=result['shape']),indent=2)+'\n')
            print('BEST',nr,117+nr,'shape',result['shape'],'macros',len(program),flush=True)
    result=dict(status='EXACT_EMISSION_AND_FINITE_COST_SEARCH',shapes=len(shapes),cases=len(results),
                elapsed_seconds=monotonic()-start,best=best,results=results)
    (b.OUT/'bundle_shapes_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print('DONE',len(results),'best',best['grammar_rules'],round(monotonic()-start,2),flush=True)

if __name__=='__main__':main()
