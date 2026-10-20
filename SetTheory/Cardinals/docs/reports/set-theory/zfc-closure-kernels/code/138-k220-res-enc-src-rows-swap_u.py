#!/usr/bin/env python3
"""Swap the two singly occurring parameters b,u in the rho8 emitter."""
import itertools,json
import search as z

def chunks(tree,lo,hi):
    found=[]
    def visit(n,st=0):
        en=st+len(z.flat(n))
        if en<=lo or st>=hi:return
        if lo<=st and en<=hi:
            assert z.s.boundary(n)==(0,0,False),(st,en)
            found.append((st,en,n));return
        assert not z.s.leaf(n)
        visit(n[0],st);visit(n[1],st+len(z.flat(n[0])))
    visit(tree)
    assert found[0][0]==lo and found[-1][1]==hi
    assert all(a[1]==b[0]for a,b in zip(found,found[1:]))
    return found

def splice(tree,lo,hi,new,insert_last=False):
    cc=chunks(tree,lo,hi);target=cc[-1][0]if insert_last else lo
    def visit(n,st=0):
        en=st+len(z.flat(n))
        if en<=lo or st>=hi:return n
        if lo<=st and en<=hi:return new if st==target else None
        left=visit(n[0],st);right=visit(n[1],st+len(z.flat(n[0])))
        return right if left is None else left if right is None else(left,right)
    return visit(tree)

def main():
    uu=z.seq([n for _,_,n in chunks(z.TREE,161,194)])
    pushb=z.MACRO[121]
    summary=[]
    for last in (False,True):
        mid=splice(z.TREE,353,379,uu)
        tt=splice(mid,161,194,pushb,last)
        assert len(z.flat(tt))==4744
        expected=z.flat(z.TREE)[:161]+z.flat(pushb)+z.flat(z.TREE)[194:353]+z.flat(uu)+z.flat(z.TREE)[379:]
        assert z.flat(tt)==expected
        # Entire changed interval remains rho8, with the same length.
        assert z.s.sites(tt)[135][0]  # materialized source is well formed
        base=z.s.sites(tt)
        for vals in itertools.permutations((3,4,5)):
            rr=[list(r)for r in base];mp=dict(zip((3,4,5),vals))
            for i in range(135,486):
                if rr[i][1]in('CI','CD')and rr[i][2]in mp:rr[i][2]=mp[rr[i][2]]
            new=z.s.tree(rr)
            assert z.s.graph_arithmetic(rr)[0]==z.s.graph_intervals(rr)
            result={'swapped':['b','u'],'register_permutation':mp,'insert_last':last,'source_metrics':z.s.metrics(new)}
            nm='rho8_swap_bu_'+''.join(map(str,vals))+('_last'if last else '_first')
            pd=z.HERE/nm;pd.mkdir(exist_ok=True);(pd/'sites.json').write_bytes(z.s.compact(rr))
            try:
                U,m=z.compile_tree(z.T,z.TREE,new);result['compiler']=m
                (pd/'candidate.tm').write_bytes(z.b.table_bytes(U))
            except Exception as e:result['error']=repr(e)
            (pd/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
            summary.append(result);print(json.dumps(result),flush=True)
    (z.HERE/'swap_u_summary.json').write_text(json.dumps(summary,indent=2)+'\n')

if __name__=='__main__':main()
