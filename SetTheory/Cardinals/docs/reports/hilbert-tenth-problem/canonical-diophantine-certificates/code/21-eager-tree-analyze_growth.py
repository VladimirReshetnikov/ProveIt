#!/usr/bin/env python3
"""Exact equality and cardinality analysis for unary L/S/F templates.
Standard library only. Reads the frozen packet; writes only its own receipt.
"""
import argparse
import collections
import functools
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PACKET = HERE

class DSU:
    def __init__(self, xs=()): self.p={x:x for x in xs}
    def find(self,x):
        if x not in self.p:self.p[x]=x
        if self.p[x]!=x:self.p[x]=self.find(self.p[x])
        return self.p[x]
    def union(self,x,y):
        a,b=self.find(x),self.find(y)
        if a!=b:self.p[b]=a

class Analysis:
    def __init__(self, data):
        self.data=data;self.nodes=data['nodes']
        self.cases={c['name']:c for c in data['cases']}
        self.step=[(r['x'],r['y']) for r in self.cases['step']['rows'] if not r['oracle']]
        self.step_row_ids=[i for i,r in enumerate(self.cases['step']['rows']) if not r['oracle']]
        self.base=[(r['x'],r['y']) for r in self.cases['base1']['rows']]
        self.dependent=[any(self.dep(x) for x in p) for p in self.step]

    @functools.cache
    def dep(self,i):
        r=self.nodes[i]
        return r[0]=='X' or any(self.dep(j) for j in r[1:])

    @functools.cache
    def head(self,i):
        c=0
        while self.nodes[i][0]=='S': c+=1;i=self.nodes[i][1]
        r=self.nodes[i]
        if r[0] in ('L','X'):return ('leaf',c,int(r[0]=='X'))
        assert r[0]=='F'
        return ('fork',c,r[1],r[2])

    @functools.cache
    def equations(self,i,j):
        """Return conjunction a*k+b*l=c, or None for structurally false."""
        x,y=self.head(i),self.head(j)
        if x[0]!=y[0]:return None
        if x[0]=='leaf':return frozenset([(x[2],-y[2],y[1]-x[1])])
        if x[1]!=y[1]:return None
        a=self.equations(x[2],y[2]);b=self.equations(x[3],y[3])
        if a is None or b is None:return None
        return a|b

    def equal_relation(self,p,q):
        eq=set()
        for i,j in zip(p,q):
            a=self.equations(i,j)
            if a is None:return {'kind':'false'}
            eq|=a
        # Constraints have only k=c, l=c, k-l=c, or 0=c.
        fixed={};delta=None
        for a,b,c in sorted(eq):
            if (a,b)==(0,0):
                if c:return {'kind':'false'}
            elif (a,b)==(1,0):
                if 'k' in fixed and fixed['k']!=c:return {'kind':'false'}
                fixed['k']=c
            elif (a,b)==(0,-1):
                if 'l' in fixed and fixed['l']!=-c:return {'kind':'false'}
                fixed['l']=-c
            else:
                assert (a,b)==(1,-1)
                if delta is not None and delta!=c:return {'kind':'false'}
                delta=c
        if delta is not None:
            if 'k' in fixed:
                l=fixed['k']-delta
                if 'l' in fixed and fixed['l']!=l:return {'kind':'false'}
                fixed['l']=l
            if 'l' in fixed:
                k=fixed['l']+delta
                if 'k' in fixed and fixed['k']!=k:return {'kind':'false'}
                fixed['k']=k
        if any(v<0 for v in fixed.values()):return {'kind':'false'}
        if len(fixed)==2:return {'kind':'point',**fixed}
        if len(fixed)==1:return {'kind':'fixed',**fixed}
        if delta is not None:return {'kind':'translation','delta':delta}
        return {'kind':'all'}

    def analyze(self):
        dep=[i for i,d in enumerate(self.dependent) if d]
        con=[i for i,d in enumerate(self.dependent) if not d]
        # Orient all stream coordinates by arbitrary representative: T_i(k)=G(k+s_i).
        relations={};dsu=DSU(dep);counts=collections.Counter()
        for a,i in enumerate(dep):
            for j in dep[a+1:]:
                r=self.equal_relation(self.step[i],self.step[j]);relations[i,j]=r;counts[r['kind']]+=1
                assert r['kind'] in ('false','point','translation')
                if r['kind']=='translation':dsu.union(i,j)
        components=collections.defaultdict(list)
        for i in dep:components[dsu.find(i)].append(i)
        groups=[];where={}
        for members in sorted(components.values(),key=min):
            rep=min(members);shifts={}
            for i in members:
                r=self.equal_relation(self.step[i],self.step[rep]);assert r['kind']=='translation'
                # k-l=delta -> l=k-delta.
                shifts[i]=-r['delta']
            gid=len(groups)
            for i,s in shifts.items():where[i]=(gid,s)
            groups.append(dict(representative=rep,members=members,shifts=shifts))
        # Fixed points: each base row and every constant step row, deduplicated structurally.
        fixed=list(self.base)+[self.step[i] for i in con]
        fdsu=DSU(range(len(fixed)))
        for i,p in enumerate(fixed):
            assert not any(self.dep(x) for x in p)
            for j,q in enumerate(fixed[:i]):
                r=self.equal_relation(p,q);assert r['kind'] in ('false','all')
                if r['kind']=='all':fdsu.union(i,j)
        freps=sorted(set(fdsu.find(i) for i in range(len(fixed))))
        frep_to_id={r:i for i,r in enumerate(freps)}
        fid={i:frep_to_id[fdsu.find(i)] for i in range(len(fixed))}
        # Point graph: its duplicate reduction is |vertices|-|components|.
        pdsu=DSU();events=[];threshold=0
        for (i,j),r in relations.items():
            if r['kind']!='point':continue
            gi,si=where[i];gj,sj=where[j]
            assert gi!=gj
            a=('g',gi,r['k']+si);b=('g',gj,r['l']+sj)
            pdsu.union(a,b);events.append(dict(kind='cross_group',i=i,j=j,**{k:r[k] for k in ['k','l']}))
            threshold=max(threshold,r['k'],r['l'])
        fixed_matches=0
        for i in dep:
            gi,si=where[i]
            for j,p in enumerate(fixed):
                r=self.equal_relation(self.step[i],p)
                assert r['kind'] in ('false','fixed')
                if r['kind']=='false':continue
                assert set(r)=={'kind','k'}
                pdsu.union(('g',gi,r['k']+si),('f',fid[j]))
                events.append(dict(kind='fixed_match',i=i,fixed=j,k=r['k']))
                threshold=max(threshold,r['k']);fixed_matches+=1
        span_sum=0
        for g in groups:
            shifts=sorted(set(g['shifts'].values()))
            span_sum+=shifts[-1]-shifts[0]+1
            threshold=max([threshold]+[b-a-1 for a,b in zip(shifts,shifts[1:])])
            g['min_shift']=shifts[0];g['max_shift']=shifts[-1]
        correction=len(pdsu.p)-len(set(pdsu.find(x) for x in list(pdsu.p)))
        intercept=span_sum+len(freps)-correction
        return dict(dependent_templates=len(dep),constant_templates=len(con),translation_groups=len(groups),
            dependent_pair_relation_counts=dict(counts),fixed_rows_before_dedup=len(fixed),fixed_distinct=len(freps),
            fixed_match_events=fixed_matches,point_graph_vertices=len(pdsu.p),
            point_graph_components=len(set(pdsu.find(x) for x in list(pdsu.p))),duplicate_correction=correction,
            sum_group_spans=span_sum,eventual_threshold_m=threshold,
            eventual_formula_m=dict(slope=len(groups),intercept=intercept),
            eventual_formula_n=dict(slope=len(groups),intercept=intercept-2*len(groups)),
            groups=groups,events=events,
            exceptional_pair_relations=[dict(i=i,j=j,**r) for (i,j),r in relations.items() if r['kind']!='false'])


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet',type=Path,default=PACKET,help='directory containing the two frozen JSON inputs')
    args=parser.parse_args()
    path=args.packet/'shared_symbolic_proofs.json';data=json.loads(path.read_text());a=Analysis(data)
    out=a.analyze();out['source_sha256']=hashlib.sha256(path.read_bytes()).hexdigest()
    out['step_row_ids']=a.step_row_ids
    (HERE/'exact_growth_receipt.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['groups','events','exceptional_pair_relations','step_row_ids']},indent=2))

if __name__=='__main__':main()
