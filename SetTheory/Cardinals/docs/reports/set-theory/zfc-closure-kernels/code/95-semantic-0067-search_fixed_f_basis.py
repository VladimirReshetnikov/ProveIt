#!/usr/bin/env python3
"""Cost unproved L_F+K and L_F+identity variants; no logical claim."""
import itertools
import json
import basis_experiment as b
import prepare_basis_routing as r
from search_basis_orientations import rename

perms=list(itertools.permutations('abc'))
Lf=b.spec['rho8_L']('a','b','c',1)
out={}
for name,extra in [('LKF',b.K),('LIF',b.I('a','a'))]:
    best=None
    variants=[]
    count=0
    extras={json.dumps(rename(extra,p)):p for p in perms}
    for lp,ep,order in itertools.product(perms,extras.values(),(False,True)):
        basis=[rename(Lf,lp),rename(extra,ep)]
        if order:basis.reverse()
        rows=basis+b.old_rows[1:]
        macro=b.prefix+[m for row in rows for m in b.tb.emit(row)]+b.tb.emit(b.bundle)+b.tb.TAIL
        actual,_=b.tb.symbolic(macro)
        assert actual==['old_top',b.spec['wal']('a','h')]+rows+[b.bundle]
        raw=''.join(b.macro_words[m] for m in macro)
        count+=1
        try:
            chunks=r.segment(raw)
            root,rules,props=r.assemble(chunks)
        except ValueError:continue
        if props[1]>6:continue
        if best is None or len(rules)<best['grammar_rules']:
            best=dict(logical_status='UNPROVED',logical_basis=name,grammar_rules=len(rules),
                      estimated_total=117+len(rules),L_parameters=lp,extra_parameters=ep,
                      extra_first=order,props=props,basis_ast=basis)
            folder=r.write_inputs(name+'_best',root,rules,props)
            (folder/'basis_ast.json').write_text(json.dumps(best,indent=2)+'\n')
            print(name,'BEST',best['grammar_rules'],lp,ep,order,flush=True)
    best['finite_variants_searched']=count
    out[name]=best
(b.OUT/'fixed_f_basis_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
