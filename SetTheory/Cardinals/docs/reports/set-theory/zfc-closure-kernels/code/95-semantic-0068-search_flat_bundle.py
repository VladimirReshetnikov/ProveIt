#!/usr/bin/env python3
"""Cost minimally equivalent flattened four-way theory bundles."""
import itertools
import json
from time import monotonic
import basis_experiment as b
import prepare_basis_routing as r

C=b.spec['bundle_C']('a','b','c')
G=b.spec['bundle_G']('a','b','c')
R=b.I(b.tb.Rel('a','b'),b.tb.All('c',b.tb.Rel('a','b')))
E=b.I(b.tb.Eq('a','b'),b.tb.All('c',b.tb.Eq('a','b')))
parts=dict(C=C,G=G,R=R,E=E)

def flat(forms):
    result=1
    for x in reversed(forms):result=b.I(x,result)
    return b.I(result,1)

def main():
    best=None
    results=[]
    start=monotonic()
    for perm in itertools.permutations('CGRE'):
        bundle=flat([parts[x] for x in perm])
        program=b.prefix+[m for row in b.old_rows for m in b.tb.emit(row)]+b.tb.emit(bundle)+b.tb.TAIL
        rows,_=b.tb.symbolic(program)
        assert rows==['old_top',b.spec['wal']('a','h')]+b.old_rows+[bundle]
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
        builder=b.recovery.builder_from_dag(b.backend,b.nodes,b.names)
        builder.sequence_lookup={s.seq:i for i,s in enumerate(builder.sequences)}
        b.tb.lower_program(builder,b.nodes,program,'flat_'+''.join(perm),shared=True)
        builder.generate();builder.tm.gc()
        count=len({q for q,bit in builder.tm.states})
        result=dict(order=''.join(perm),bundle_ast=bundle,AX_macro_count=len(program),
                    AX_min_dictionary_calls=len(b.spelling(raw)),
                    fine_operations=len(b.expansion(raw)),
                    named_Wade_states=count,grammar_rules=nr,
                    estimated_working_states=117+nr,props=props,
                    exact_symbolic_AXIOM_stack=True,
                    logical_status='Equivalent fixed bundle in minimal implication, with arbitrary relative falsity')
        results.append(result)
        if best is None or nr<best['grammar_rules']:
            best=result
            folder=r.write_inputs('flat_bundle_best',root,rules,props)
            (folder/'basis_ast.json').write_text(json.dumps(dict(basis_ast=[b.old_rows[0]],bundle_ast=bundle,
                 helper_rows=8,retains_u=True,logical_status=result['logical_status'],order=''.join(perm)),indent=2)+'\n')
            print('BEST',nr,117+nr,'order',''.join(perm),'Wade',count,'macros',len(program),flush=True)
    result=dict(status='EXACT_EMISSION_AND_FINITE_COST_SEARCH',cases=len(results),
                elapsed_seconds=monotonic()-start,best=best,results=results)
    (b.OUT/'flat_bundle_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print('DONE',len(results),'best',best['grammar_rules'],round(monotonic()-start,2),flush=True)

if __name__=='__main__':main()
