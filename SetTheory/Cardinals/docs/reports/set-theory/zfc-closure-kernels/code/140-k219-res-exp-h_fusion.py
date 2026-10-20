#!/usr/bin/env python3
"""Safe fusion of equality existence with G, deleting one actual row.

H = not forall x (E(x,y) -> not forall x G).
This is exactly exists x(E(x,y) and forall x G), hence the two old rows
are recovered by existential monotonicity and rho6, with no T assumption.
"""
import collections,itertools,json
import additive_binder as z

OUT=z.ROOT/'research_calculus/generated/h_fusion'
INC=('CI',1);IMP=z.q(90);NEG=z.q(184)
M={166:z.q(98),121:z.q(12),168:z.q(166),177:NEG[0],119:IMP,
   180:(IMP,(INC,INC)),181:(IMP,INC),182:(IMP,((INC,INC),INC)),218:NEG}
G=[168,166,182,168,121,182,166,121,181,166,121,182,180,119,119]

def splice(tree,lo,hi,new):
    used=[]
    def walk(t,i=0):
        j=i+len(z.flat(t))
        if j<=lo or i>=hi:return t
        if lo<=i and j<=hi:
            assert z.s.boundary(t)==(0,0,False),(i,j,z.s.boundary(t))
            if i==lo:used.append(i);return new
            return None
        assert not z.s.leaf(t)
        a=walk(t[0],i);b=walk(t[1],i+len(z.flat(t[0])))
        return b if a is None else a if b is None else(a,b)
    r=walk(tree);assert used==[lo]
    return r

def source(h,where):
    if where=='G':
        t=splice(z.TREE,2419,2650,None)
        return splice(t,486,895,h)
    if where=='rho1':
        t=splice(z.TREE,2419,2650,h)
        return splice(t,486,895,None)
    raise ValueError(where)

def main():
    OUT.mkdir(parents=True,exist_ok=True);res=[]
    for perm in itertools.permutations([166,121,168]):
        rename=dict(zip([166,121,168],perm));gg=[rename.get(x,x)for x in G]
        for x,y in itertools.permutations([166,121,168],2):
            word=[x,x,y,182,x]+gg+[180,218,119,180,218]
            h=z.serial([M[m]for m in word]);assert z.s.boundary(h)==(0,0,False)
            for where in ['G','rho1']:
                t=source(h,where);sites=z.s.sites(t)
                assert z.s.graph_arithmetic(sites)[0]==z.s.graph_intervals(sites)
                nm='p'+''.join(str(i)for i in perm)+f'_x{x}_y{y}_{where}'
                d=OUT/nm;d.mkdir(exist_ok=True)
                result=dict(name=nm,formula='not forall x (E(x,y) -> not forall x G)',
                            G_parameter_permutation=perm,existence_parameters=[x,y],
                            H_postfix=word,placement=where,source_metrics=z.s.metrics(t),
                            removed_row_count=1,old_stack_output_count=10,new_stack_output_count=9)
                (d/'sites.json').write_bytes(z.s.compact(sites))
                try:
                    T,m=z.compile_tree(z.T,z.TREE,t);result['compiler']=m
                    (d/'candidate.tm').write_bytes(z.b.table_bytes(T))
                except Exception as e:result['compile_error']=repr(e)
                (d/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');res.append(result)
                print(json.dumps({k:v for k,v in result.items()if k!='H_postfix'}),flush=True)
    (OUT/'summary.json').write_text(json.dumps(res,indent=2)+'\n')

if __name__=='__main__':main()
