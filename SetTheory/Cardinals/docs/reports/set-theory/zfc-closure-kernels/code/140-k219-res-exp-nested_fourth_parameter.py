#!/usr/bin/env python3
"""Read rho8's unique fourth parameter from a nested existing AX parameter.

Let x=P(u,s).  The first emitted row becomes
((p -> u) -> r) -> ((r -> p) -> (s -> p)).
The ordinary u-reader unpairs x in place, leaving s in its register.
All later rows use the unpaired parameter.  The c-register choice preserves
their post-decoding parameters while permuting rho8's parameter roles.
The axiom families are unchanged; individual emitted batches differ.
"""
import itertools,json
import orientation_postfix as o
z=o.z
OUT=z.ROOT/'research_calculus/generated/nested_fourth_parameter'

def make(pairreg,preg,rreg):
    ren={3:preg,4:rreg,5:pairreg,8:pairreg}
    rows=[list(x)for x in z.ROWS]
    for i in range(135,486):
        if rows[i][1]in('CI','CD')and rows[i][2]in ren:rows[i][2]=ren[rows[i][2]]
    tree=z.s.tree(rows)
    assert z.s.graph_arithmetic(rows)[0]==z.s.graph_intervals(rows)
    return tree

def main():
    OUT.mkdir(parents=True,exist_ok=True);summary=[]
    for pairreg,preg,rreg in itertools.permutations([3,4,5]):
        tree=make(pairreg,preg,rreg);name=f'pair{pairreg}_p{preg}_r{rreg}'
        dest=OUT/name;dest.mkdir(exist_ok=True);rows=z.s.sites(tree)
        (dest/'sites.json').write_bytes(z.s.compact(rows))
        result=dict(name=name,pair_register=pairreg,repeated_p_register=preg,repeated_r_register=rreg,
                    source_metrics=z.s.metrics(tree),fourth_field='nested into an existing parameter, consumed in rho8')
        try:
            table,m=z.compile_tree(z.T,z.TREE,tree);result['compiler']=m
            (dest/'candidate.tm').write_bytes(z.b.table_bytes(table))
        except Exception as e:result['compile_error']=repr(e)
        (dest/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');summary.append(result)
        print(json.dumps(result),flush=True)
    (OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')

if __name__=='__main__':main()
