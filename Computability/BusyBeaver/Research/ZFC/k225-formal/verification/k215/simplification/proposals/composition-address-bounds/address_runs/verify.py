#!/usr/bin/env python3
"""Verify the exact source recipe, CFG equality, and closed-class obstruction."""
from pathlib import Path
from functools import cache
import hashlib,json
import source_language as s
import source_capacity as cap
HERE=Path(__file__).resolve().parent

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    cert=json.loads((HERE/'rotation_certificate.json').read_text())
    baseline=HERE/'baseline_sites215.json';target=HERE/'sites_zero5_206.json'
    assert digest(baseline)==cert['baseline_sha256']
    assert digest(target)==cert['target_sha256']
    rows=json.loads(baseline.read_text());expected=json.loads(target.read_text())
    base=s.tree(rows);goal=s.tree(expected)
    N=[tuple(n)for n in cert['nodes']];index={n:i for i,n in enumerate(N)}
    assert len(index)==len(N)
    for i,n in enumerate(N):
        assert len(n)==2
        if isinstance(n[0],str):assert n[0]in ('CI','CD','CB','CC','CH')
        else:assert all(type(k)is int and 0<=k<i for k in n)
    @cache
    def dec(n):return N[n]if isinstance(N[n][0],str)else tuple(dec(k)for k in N[n])
    def intern(n):
        if n not in index:index[n]=len(N);N.append(n)
        return index[n]
    def branch(n):return not isinstance(N[n][0],str)
    def closed(n):return s.boundary(dec(n))==(0,0,False)
    def legal(old,new):
        if not branch(old)or not branch(new):return False
        a,right=N[old];left,c=N[new]
        return branch(right)and branch(left)and N[right][1]==c and N[left][0]==a and N[right][0]==N[left][1] and all(closed(t)for t in(a,N[right][0],c))
    def rewrite(root,old,new):
        memo={}
        def go(n):
            if n==old:return new,1
            if not branch(n):return n,0
            if n not in memo:
                l,x=go(N[n][0]);r,y=go(N[n][1]);memo[n]=(intern((l,r)),x+y)
            return memo[n]
        return go(root)
    root=cert['root'];assert dec(root)==base
    graph=s.graph_intervals(rows);assert s.graph_arithmetic(rows)[0]==graph
    stages=[]
    for ordinal,(old,new)in enumerate(cert['rotations'],1):
        assert legal(old,new)or legal(new,old),ordinal
        root,occurrences=rewrite(root,old,new);assert occurrences>0
        rr=s.sites(dec(root))
        assert [r[1:]for r in rr]==[r[1:]for r in rows]
        assert s.graph_intervals(rr)==s.graph_arithmetic(rr)[0]==graph
        stages.append({'rotation':ordinal,'replaced_occurrences':occurrences,'metrics':s.metrics(dec(root))})
    assert dec(root)==goal==dec(cert['target'])
    assert s.compact(s.sites(dec(root)))==target.read_bytes()
    metrics=s.metrics(goal);assert metrics=={'dag_nodes':206,'leaf_occurrences':4751,'maximum_depth':43,'maximum_zero_run':5}
    fragment=s.subtree(base,'1101001001111');spine=[];t=fragment
    for _ in range(5):
        assert not s.leaf(t)
        bs=[s.boundary(c)for c in t]
        assert any(b!=(0,0,False)for b in bs)
        spine.append(bs);t=t[0]
    assert t==('CD',5)
    original=cap.encode(base)
    c4,_,_,_=cap.solve(original,4);c5,_,_,_=cap.solve(original,5)
    assert c4==-1 and c5==2
    out={'status':'PASS','source_sha256':digest(target),'baseline_sha256':digest(baseline),'certificate_bytes':(HERE/'rotation_certificate.json').stat().st_size,'certificate_nodes':len(cert['nodes']),'global_rotations':len(stages),'baseline_metrics':s.metrics(base),'target_metrics':metrics,'primitive_word_entries':len(rows),'guarded_CFG_edges':sum(len(g[1])for g in graph),'dual_CFG_equality_at_every_rotation':True,'minimum_zero_run_under_closed_reassociation':5,'four_zero_capacity':c4,'five_zero_capacity':c5,'fixed_spine':{'source_prefix':'1101001001111','first_ordinal':4578,'last_ordinal':4590,'left_edge_count':5,'terminal_leaf':['CD',5],'child_boundaries':spine},'stages':stages,'scope':'Exact source-layout and ordinary closed-associativity theorem certificates. No allocated binary machine or new Lean/Rocq endpoint.'}
    (HERE/'evidence/verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items()if k not in('stages','fixed_spine')},indent=2))
if __name__=='__main__':main()
