#!/usr/bin/env python3
"""Independently check emitted source structure and reported source costs.

This checks a changed AX word against its explicitly named schema permutations.
It does not check a binary machine or internal ZFC calibration.
"""
from pathlib import Path
from functools import lru_cache
import argparse,json,hashlib
import source_model as model

HERE=Path(__file__).resolve().parent
class Tree:
    def __init__(self, data):
        self.root=data['root'];self.nodes={int(i):tuple(tuple(e) for e in es) for i,es in data['nodes'].items()}
        self.reached=set();self.active=set()
        for es in self.nodes.values():
            assert len(es)==2
            for e in es:
                assert e[0] in ('N','I','D','B','C','H')
                assert len(e)==(1 if e[0]=='H' else 2)
                if len(e)>1:assert isinstance(e[1],int) and e[1]>=0
                if e[0] in ('I','D'):assert e[1]<9
                if e[0]=='N':assert e[1] in self.nodes
        self.norm(('N',self.root));assert self.reached==set(self.nodes)
    @lru_cache(None)
    def bounds(self,e):
        if e[0]!='N':return (e[1] if e[0]=='B' else int(e[0]=='D'),e[1] if e[0]=='C' else 0)
        # Acyclicity separately checked by norm; input depths here are small.
        a,b=self.nodes[e[1]];ab,ac=self.bounds(a);bb,bc=self.bounds(b)
        return max(ab-1,bb),max(ac,bc-1)
    @lru_cache(None)
    def norm(self,e):
        if e[0]!='N':return e
        assert e[1] not in self.active,'cyclic source'
        self.reached.add(e[1]);self.active.add(e[1]);a,b=self.nodes[e[1]]
        aa,bb=self.norm(a),self.norm(b);self.active.remove(e[1])
        if self.bounds(a)==self.bounds(b)==(0,0):
            return ('S',*(aa[1:] if aa[0]=='S' else (aa,)),*(bb[1:] if bb[0]=='S' else (bb,)))
        return ('A',aa,bb)
    @lru_cache(None)
    def metric(self,e):
        if e[0]!='N':return 0,0,0,1,int(e[0]=='D')
        a,b=map(self.metric,self.nodes[e[1]]);leading=a[0]+1
        return leading,max(leading,a[1],b[1]),1+max(a[2],b[2]),a[3]+b[3],a[4]+b[4]

def permute(f,perm,swap_u_b=False):
    if isinstance(f,tuple):return f[0],permute(f[1],perm,swap_u_b),permute(f[2],perm,swap_u_b)
    if swap_u_b:f={'u':'b','b':'u'}.get(f,f)
    return dict(zip(('a','b','c'),perm)).get(f,f)

def expected_ax(order,roles,u_b_swap):
    assert sorted(order)==list(range(8))
    assert len(roles)==8 and all(type(r) is int and 0<=r<6 for r in roles)
    from itertools import permutations
    perms=tuple(permutations(('a','b','c')))
    rows=[]
    for i,formula in enumerate(model.ROWS[1:]):
        moved=permute(formula,perms[roles[i]],u_b_swap and i==0)
        macros=model.emit(moved)
        assert macros.count(158)==int(i==0),'exactly one u read in the sole four-argument schema'
        assert macros.count(208)==int(i==0),'exactly one move from u'
        rows.append(tuple(t for m in macros for t in model.MACROS[m]))
    prefix=tuple(t for m in [166,121,180,176] for t in model.MACROS[m])
    old=model.normal(('N',183))[1:]
    oldlogical=prefix+sum((tuple(t for m in model.emit(f) for t in model.MACROS[m]) for f in model.ROWS[1:]),())
    assert old[:len(oldlogical)]==oldlogical
    return ('S',*(prefix+sum((rows[i] for i in order),())+old[len(oldlogical):]))

def check(path,order,roles,u_b_swap=False):
    data=json.loads(path.read_text());tree=Tree(data)
    wanted=expected_ax(order,roles,u_b_swap)
    @lru_cache(None)
    def expected(e):
        if e==('N',183):return wanted
        if e[0]!='N':return e
        l,r=model.NODES[e[1]];ll,rr=expected(l),expected(r)
        if model.bounds(l)==model.bounds(r)==(0,0):
            return ('S',*(ll[1:] if ll[0]=='S' else (ll,)),*(rr[1:] if rr[0]=='S' else (rr,)))
        return ('A',ll,rr)
    assert tree.norm(('N',tree.root))==expected(('N',model.DATA['root']))
    leading,zero,depth,leaves,decrements=tree.metric(('N',tree.root))
    return dict(path=path.name,status='PASS',source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),source_nodes=len(tree.nodes),leading_zero_depth=leading,maximum_zero_run=zero,maximum_leaf_depth=depth,instruction_leaves=leaves,decrement_occurrences=decrements,whole_source_normal_form_exact=True,order=order,roles=roles,u_b_swap=u_b_swap,binary_state_claim=False)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=HERE/'candidate_verification.json');args=ap.parse_args()
    records=[]
    records.append(check(HERE/'data/sparse201.json',list(range(8)),[0]*8))
    records.append(check(HERE/'novel_candidates/candidate_1_202.json',list(range(8)),[2]+[0]*7))
    records.append(check(HERE/'focused_milp_results/dictionary_max24_freq2_zero7_depth64_old1.json',list(range(8)),[2]+[0]*7))
    result=dict(status='PASS',scope='Independent whole-source structure check and exact source counts; schema permutation meaning is a separate theorem, and binary compilation is not asserted.',records=records)
    args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
