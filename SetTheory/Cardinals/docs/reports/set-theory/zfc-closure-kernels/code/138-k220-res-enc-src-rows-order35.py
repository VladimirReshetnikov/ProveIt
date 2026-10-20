#!/usr/bin/env python3
"""Swap equal-length rho3/rho5 rows without altering control or tree shape."""
import json,sys
import search as z

def main():
    original=z.TREE
    rr=[r.copy()for r in z.ROWS]
    # Both words have identical constructor skeleton.  Replacing each
    # scalar push by the corresponding push of the other row alters only
    # the immutable parameter register copied by that closed macro.
    for dst,src in [('rho3','rho5'),('rho5','rho3')]:
        dlo,dhi=z.INTERVALS[dst]
        sw=z.WORDS[src];dw=z.WORDS[dst]
        assert len(sw)==len(dw)
        at=dlo
        for dm,sm in zip(dw,sw):
            old=z.flat(z.MACRO[dm]);new=z.flat(z.MACRO[sm])
            assert len(old)==len(new)
            assert tuple(tuple(r[1:])for r in rr[at:at+len(old)])==old
            for i,(p,q)in enumerate(zip(old,new)):
                if p!=q:
                    assert p[0]==q[0] and p[0]in('CI','CD') and p[1]in(3,4,5)and q[1]in(3,4,5)
                    rr[at+i][2]=q[1]
            at+=len(old)
        assert at==dhi
    new=z.s.tree(rr);gg=z.s.graph_arithmetic(rr)[0]
    assert gg==z.s.graph_intervals(rr)
    assert[x[1]for x in gg]==[x[1]for x in z.GRAPH]
    out=z.HERE/'order35';out.mkdir(exist_ok=True)
    (out/'sites.json').write_bytes(z.s.compact(rr))
    first={'order_swap':['rho3','rho5'],'source_metrics':z.s.metrics(new)}
    try:
        U,m=z.compile_tree(z.T,original,new);first['compiler']=m
        (out/'candidate.tm').write_bytes(z.b.table_bytes(U))
    except Exception as e:first['error']=repr(e)
    (out/'receipt.json').write_text(json.dumps(first,indent=2)+'\n')
    print(json.dumps(first),flush=True)
    # Search all row-parameter choices for this different logical-row order.
    z.ROWS=rr;z.TREE=new;z.GRAPH=gg;z.HERE=out
    import exhaustive as e
    e.main()
    summary=json.loads((out/'exhaustive_summary.json').read_text())
    if summary['minimum_dag_nodes']<=208:
        for num,v in enumerate(summary['minimizers']):
            perms=e.j.as_perms(v);rr,nn=z.changed(perms)
            dest=out/f'minimizer_{num}';dest.mkdir(exist_ok=True)
            (dest/'sites.json').write_bytes(z.s.compact(rr))
            result={'permutations':perms,'source_metrics':z.s.metrics(nn)}
            try:
                U,m=z.compile_tree(z.T,original,nn);result['compiler']=m
                (dest/'candidate.tm').write_bytes(z.b.table_bytes(U))
            except Exception as ee:result['error']=repr(ee)
            (dest/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
            print(json.dumps(result),flush=True)

if __name__=='__main__':main()
