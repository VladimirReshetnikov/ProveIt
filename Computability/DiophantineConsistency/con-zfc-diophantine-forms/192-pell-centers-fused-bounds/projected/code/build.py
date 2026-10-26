#!/usr/bin/env python3
"""Replace two independent ternary guards by one reciprocal budget.

Only canonical-witness completeness is claimed.  The change is not a
pointwise bijection between all old and new zeros.  See proofs/FUSION.md.
"""
from pathlib import Path
import hashlib, json, random

ROOT=Path(__file__).resolve().parents[1]
GUARDS=set(range(207,213))
DELETED={210,211,212}
ORDINATES=[142,151,154,157,160,163,166,169,172,175,178,181,187]
REMAINDERS=[104,108,111,114,117,121,124,128,132,135]

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def canonical(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()

class Graph:
    def __init__(self):self.nodes=[];self.ids={}
    def node(self,op,*a):
        key=(op,*a)
        if key not in self.ids:
            self.ids[key]=len(self.nodes);self.nodes.append(list(key))
        return self.ids[key]
    def c(self,n):return self.node('const',n)
    def add(self,a,b):
        if a==self.c(0):return b
        if b==self.c(0):return a
        return self.node('+',a,b)
    def sub(self,a,b):
        if b==self.c(0):return a
        return self.node('-',a,b)
    def mul(self,a,b):
        if a==self.c(1):return b
        if b==self.c(1):return a
        if self.c(0) in (a,b):return self.c(0)
        return self.node('*',a,b)
    def sq(self,a):return self.mul(a,a)
    def sum(self,aa):
        out=self.c(0)
        for a in aa:out=self.add(out,a)
        return out

def certificates(nodes,roots,output,inputs):
    prime=1000000007;ds=[];tops=[];heights=[]
    for n in nodes:
        op=n[0]
        if op=='const':
            ds.append(0);tops.append(n[1]%prime)
            heights.append((abs(n[1])-1).bit_length() if n[1] else 0)
        elif op=='var':
            ds.append(1);tops.append((inputs[n[1]]+3)%prime);heights.append(0)
        else:
            a,b=n[1:]
            if op=='*':
                ds.append(ds[a]+ds[b]);tops.append(tops[a]*tops[b]%prime)
                heights.append(heights[a]+heights[b])
            else:
                d=max(ds[a],ds[b]);ds.append(d)
                av=tops[a] if ds[a]==d else 0;bv=tops[b] if ds[b]==d else 0
                tops.append((av+bv if op=='+' else av-bv)%prime)
                heights.append(max(heights[a],heights[b])+1)
    bound=max(ds[r] for r in roots)
    witnesses=[i for i,r in enumerate(roots) if ds[r]==bound and tops[r]]
    if not witnesses:raise ValueError('No top-degree witness')
    dc={'degree':2*bound,'modulus':prime,'input_direction':[i+3 for i in inputs],
        'residual_degree_bounds':[ds[r] for r in roots],
        'witness_residual':witnesses[0],
        'witness_top_residue':tops[roots[witnesses[0]]],
        'coefficient_height_at_most_power_of_two':max(2*heights[r] for r in roots)+(len(roots)-1).bit_length()}
    rng=random.Random(20261026)
    for trial in range(8):
        point=[rng.randrange(1,prime) for _ in inputs];values=[]
        for n in nodes:
            op=n[0]
            if op=='const':v=n[1]
            elif op=='var':v=point[n[1]]
            elif op=='+':v=values[n[1]]+values[n[2]]
            elif op=='-':v=values[n[1]]-values[n[2]]
            else:v=values[n[1]]*values[n[2]]
            values.append(v%prime)
        adj=[0]*len(nodes);adj[output]=1;grad=[0]*len(inputs)
        for i in range(len(nodes)-1,-1,-1):
            n=nodes[i];op=n[0];a=adj[i]
            if op=='var':grad[n[1]]=(grad[n[1]]+a)%prime
            elif op=='const':pass
            elif op=='+':
                adj[n[1]]=(adj[n[1]]+a)%prime;adj[n[2]]=(adj[n[2]]+a)%prime
            elif op=='-':
                adj[n[1]]=(adj[n[1]]+a)%prime;adj[n[2]]=(adj[n[2]]-a)%prime
            else:
                adj[n[1]]=(adj[n[1]]+a*values[n[2]])%prime
                adj[n[2]]=(adj[n[2]]+a*values[n[1]])%prime
        if all(grad):
            dep={'modulus':prime,'point':point,'gradient':grad}
            return dc,dep
    raise ValueError('No complete dependence certificate')

def build(path):
    old=json.loads(path.read_text());oldnodes=old['nodes']
    index=[v['source_index'] for v in old['variables']]
    if not GUARDS<=set(index):raise ValueError('Guard variables not free')
    if not {150,151} <= set(old['retained_source_rows']):raise ValueError('Missing guard row')
    oldvalues={v:next(j for j,n in enumerate(oldnodes) if n==['var',i]) for i,v in enumerate(index)}
    oldvalues.update({d['variable']:d['root'] for d in old['definitions']})
    olddep=[]
    for n in oldnodes:
        if n[0]=='const':olddep.append(set())
        elif n[0]=='var':olddep.append({index[n[1]]})
        else:olddep.append(olddep[n[1]]|olddep[n[2]])
    keep=[i for i,r in enumerate(old['retained_source_rows']) if r not in (150,151)]
    keep.append(len(old['residual_roots'])-1) # joint certificate
    if any(olddep[old['residual_roots'][i]]&GUARDS for i in keep):
        raise ValueError('A guard occurs in a retained equation')
    needed={16,126,184,*ORDINATES,*REMAINDERS}
    if any(olddep[oldvalues[v]]&GUARDS for v in needed):
        raise ValueError('A reconstructed semantic coordinate depends on a guard')
    inputs=[v for v in index if v not in DELETED]
    pos={v:i for i,v in enumerate(inputs)};g=Graph();mapping={}
    def imp(i):
        if i in mapping:return mapping[i]
        n=oldnodes[i];op=n[0]
        if op=='const':out=g.c(n[1])
        elif op=='var':out=g.node('var',pos[index[n[1]]])
        else:out=g.node(op,imp(n[1]),imp(n[2]))
        mapping[i]=out;return out
    def x(v):return imp(oldvalues[v])
    roots=[imp(old['residual_roots'][i]) for i in keep]
    C=g.mul(g.c(2),x(16));U=g.sq(x(126));V=g.sq(x(184))
    ys=[g.sub(x(v),g.c(1)) if v==154 else x(v) for v in ORDINATES]
    E=g.sum([g.c(1),g.sq(C),*(g.sq(y) for y in ys)])
    R=g.mul(g.c(4),g.sum(g.sq(x(v)) for v in REMAINDERS))
    guard=g.sum([g.sq(x(207)),g.sq(x(208)),g.mul(x(209),g.add(x(209),g.c(1)))])
    fused=g.sub(g.sub(g.sub(g.sub(g.mul(U,V),g.mul(U,E)),g.mul(V,R)),g.c(1)),guard)
    roots.append(fused)
    output=g.sum(g.sq(r) for r in roots)
    dc,dep=certificates(g.nodes,roots,output,inputs)
    live=set()
    def walk(i):
        if i in live:return
        live.add(i);n=g.nodes[i]
        if n[0] in ('+','-','*'):walk(n[1]);walk(n[2])
    walk(output)
    metrics={'variables':len(inputs),'residuals':len(roots),'degree':dc['degree'],
             'live_binary_operations':sum(g.nodes[i][0] in ('+','-','*') for i in live),
             'maximum_literal_absolute_value':max(abs(g.nodes[i][1]) for i in live if g.nodes[i][0]=='const'),
             'coefficient_height_bound_exponent':dc['coefficient_height_at_most_power_of_two']}
    out={'schema':'conzfc-guard-fusion-v1','domain':'unrestricted integers',
        'parent_file':path.name,'parent_sha256':digest(path),
        'variables':[v for v in old['variables'] if v['source_index'] not in DELETED],
        'deleted_source_indices':sorted(DELETED),
        'changed_role_source_indices':[207,208,209],
        'retained_parent_residual_indices':keep,
        'source_value_nodes':{str(v):x(v) for v in sorted(needed|{207,208,209})},
        'fusion_nodes':dict(C=C,U=U,V=V,E=E,R=R,guard=guard,residual=fused),
        'nodes':g.nodes,'residual_roots':roots,'output':output,
        'degree_certificate':dc,'dependency_certificate':dep,'metrics':metrics}
    return out

def main():
    results=[]
    for path in sorted((ROOT/'sources').glob('integer*_linear.json')):
        d=build(path);m=d['metrics'];suffix='_linear' if path.name.endswith('_linear.json') else ''
        name=f"integer{m['variables']}_degree{m['degree']}{suffix}.json"
        (ROOT/'equations'/name).write_bytes(canonical(d))
        results.append(dict(file=name,**m));print(json.dumps(results[-1]))
    (ROOT/'equations/RESULTS.json').write_bytes(canonical(results))
if __name__=='__main__':main()
