#!/usr/bin/env python3
"""Finite parameter/orientation search for a complete K/S/Peirce replacement."""
import itertools
import json
from time import monotonic
import basis_experiment as b
import prepare_basis_routing as r

def rename(x,perm):
    if isinstance(x,tuple):return tuple(rename(y,perm) for y in x)
    return dict(zip('abc',perm)).get(x,x)

def main():
    perms=list(itertools.permutations('abc'))
    origins=dict(K=b.K,S=b.S,P=b.P)
    fixed=b.old_rows[1:]
    best=10**9
    winners=[]
    total=0
    start=monotonic()
    for kp,sp,pp in itertools.product(perms,repeat=3):
        forms=dict(K=rename(b.K,kp),S=rename(b.S,sp),P=rename(b.P,pp))
        for order in itertools.permutations('KSP'):
            rows=[forms[x] for x in order]+fixed
            macro=b.prefix+[m for row in rows for m in b.tb.emit(row)]+b.tb.emit(b.bundle)+b.tb.TAIL
            raw=''.join(b.macro_words[m] for m in macro)
            total+=1
            try:
                chunks=r.segment(raw)
                root,rules,props=r.assemble(chunks)
            except ValueError:
                continue
            if props[1]>6:continue
            count=len(rules)
            if count<=best:
                desc=dict(K=''.join(kp),S=''.join(sp),P=''.join(pp),order=''.join(order),
                          rules_count=count,props=props,basis_ast=[forms[x] for x in order])
                if count<best:
                    winners=[]
                    best=count
                    print('BEST',best,'total',total,'seconds',round(monotonic()-start,2),desc,flush=True)
                winners.append(desc)
                if len(winners)==1:
                    actual,_=b.tb.symbolic(macro)
                    assert actual==['old_top',b.spec['wal']('a','h')]+rows+[b.bundle]
                    folder=r.write_inputs('KSP_best',root,rules,props)
                    (folder/'basis_ast.json').write_text(json.dumps(desc,indent=2)+'\n')
            if total%100==0:print('progress',total,'best',best,'seconds',round(monotonic()-start,2),flush=True)
    out=dict(cases=total,minimum_grammar_rules=best,framework_working_states=117,
             estimated_working_states=best+117,method='current dictionary parse, then constrained binary assembly; not global optimum',
             elapsed_seconds=monotonic()-start,winners=winners)
    (b.OUT/'basis_orientation_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print('DONE',total,best,round(monotonic()-start,2),flush=True)

if __name__=='__main__':main()
