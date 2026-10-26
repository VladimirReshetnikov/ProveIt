#!/usr/bin/env python3
"""Independent finite verifier; imports no producer or parent search code."""
from pathlib import Path
from collections import Counter
import copy, hashlib, json

ROOT=Path(__file__).resolve().parents[1]
GUARDS=set(range(207,213));REMOVED={210,211,212}
YS=[142,151,154,157,160,163,166,169,172,175,178,181,187]
RS=[104,108,111,114,117,121,124,128,132,135]
def need(x,msg):
    if not x:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def add(a,b,sgn=1):
    r=a.copy()
    for m,c in b.items():
        r[m]=r.get(m,0)+sgn*c
        if not r[m]:del r[m]
    return r
def times(a,b):
    r={}
    for m,c in a.items():
        for n,d in b.items():
            k=tuple(sorted(m+n));r[k]=r.get(k,0)+c*d
    return {m:c for m,c in r.items() if c}
def const(c):return {():c} if c else {}
def v(i):return {(i,):1}
def sq(a):return times(a,a)
def summ(aa):
    out={}
    for a in aa:out=add(out,a)
    return out
def g3(a,b,c):return summ([sq(v(a)),sq(v(b)),times(v(c),add(v(c),const(1)))])

def frozen_guard_polys():
    U=sq(v(126));V=sq(v(184));C=times(const(2),v(16))
    E=summ([const(1),sq(C)]+[sq(add(v(i),const(-1)) if i==154 else v(i)) for i in YS])
    R=times(const(4),summ([sq(v(i)) for i in RS]))
    return U,V,E,R

def signatures(nodes,indices,pool):
    hashes=[];deps=[]
    for i,n in enumerate(nodes):
        op=n[0]
        need(op in ('const','var','+','-','*'),'Unknown instruction')
        if op=='const':
            need(type(n[1]) is int,'Noninteger literal');entry=('c',n[1]);d=set()
        elif op=='var':
            need(type(n[1]) is int and 0<=n[1]<len(indices),'Bad input index')
            entry=('v',indices[n[1]]);d={indices[n[1]]}
        else:
            need(len(n)==3 and all(type(j) is int and 0<=j<i for j in n[1:]),'Not an acyclic circuit')
            entry=(op,hashes[n[1]],hashes[n[2]]);d=deps[n[1]]|deps[n[2]]
        if entry not in pool:pool[entry]=len(pool)
        hashes.append(pool[entry]);deps.append(d)
    return hashes,deps

def eval_poly(nodes,root,atoms):
    memo={}
    def ev(i):
        if i in atoms:return v(atoms[i])
        if i in memo:return memo[i]
        n=nodes[i];op=n[0]
        if op=='const':out=const(n[1])
        elif op=='var':raise ValueError('Unexpected free atom in fused residual')
        elif op=='+':out=add(ev(n[1]),ev(n[2]))
        elif op=='-':out=add(ev(n[1]),ev(n[2]),-1)
        else:out=times(ev(n[1]),ev(n[2]))
        memo[i]=out;return out
    return ev(root)

def check(d,parent,source):
    inds=[x['source_index'] for x in d['variables']]
    oldinds=[x['source_index'] for x in parent['variables']]
    need(inds==[i for i in oldinds if i not in REMOVED],'Free coordinate order')
    need(set(d['deleted_source_indices'])==REMOVED,'Deleted coordinates')
    need(d['changed_role_source_indices']==[207,208,209],'Guard role change')
    pool={}
    hs,dp=signatures(d['nodes'],inds,pool);oh,od=signatures(parent['nodes'],oldinds,pool)
    oldvals={oldinds[n[1]]:i for i,n in enumerate(parent['nodes']) if n[0]=='var'}
    oldvals.update({r['variable']:r['root'] for r in parent['definitions']})
    for definition in parent['definitions']:
        need(not od[definition['root']] & GUARDS,'Private guard occurs in an eliminated definition')
    required={16,126,184,207,208,209,*YS,*RS}
    need(set(map(int,d['source_value_nodes']))==required,'Incomplete semantic ports')
    for s,n in d['source_value_nodes'].items():
        k=int(s);need(hs[n]==oh[oldvals[k]],'Changed semantic coordinate')
        if k not in GUARDS:need(not od[oldvals[k]]&GUARDS,'Guard used in reconstruction')
    keep=[i for i,r in enumerate(parent['retained_source_rows']) if r not in (150,151)]
    keep.append(len(parent['residual_roots'])-1)
    need(d['retained_parent_residual_indices']==keep,'Wrong retained-row partition')
    need(len(d['residual_roots'])==len(keep)+1,'Residual count')
    for newroot,oldi in zip(d['residual_roots'],keep):
        oldroot=parent['residual_roots'][oldi]
        need(hs[newroot]==oh[oldroot],'Retained residual changed')
        need(not od[oldroot]&GUARDS,'An old guard is not private')
    U,V,E,R=frozen_guard_polys()
    oldcap=add(add(V,E,-1),g3(207,208,209),-1)
    oldrem=add(add(add(U,R,-1),const(1),-1),g3(210,211,212),-1)
    def sparse(r):return {tuple(m):c for c,m in r['terms']}
    need(sparse(source['residuals'][150])==oldcap,'Source cap meaning')
    need(sparse(source['residuals'][151])==oldrem,'Source remainder meaning')
    expected=add(add(add(add(times(U,V),times(U,E),-1),times(V,R),-1),const(1),-1),g3(207,208,209),-1)
    atoms={n:int(k) for k,n in d['source_value_nodes'].items()}
    need(len(atoms)==len(required),'Aliased semantic ports')
    need(eval_poly(d['nodes'],d['residual_roots'][-1],atoms)==expected,'Fused residual identity')
    need(d['fusion_nodes']['residual']==d['residual_roots'][-1],'Wrong fused node')
    # The output must be precisely the sum of the declared residual squares.
    def squares(i):
        n=d['nodes'][i]
        if n[0]=='+':return squares(n[1])+squares(n[2])
        need(n[0]=='*' and n[1]==n[2],'Output is not a sum of squares')
        return [n[1]]
    need(Counter(squares(d['output']))==Counter(d['residual_roots']),'Output square list')
    dc=d['degree_certificate'];p=dc['modulus']
    need(p==1000000007,'Degree prime changed')
    need(dc['input_direction']==[i+3 for i in inds],'Degree direction')
    degree=[];lead=[];height=[]
    for n in d['nodes']:
        op=n[0]
        if op=='var':degree.append(1);lead.append((inds[n[1]]+3)%p);height.append(0)
        elif op=='const':
            degree.append(0);lead.append(n[1]%p);height.append((abs(n[1])-1).bit_length() if n[1] else 0)
        else:
            a,b=n[1:]
            if op=='*':degree.append(degree[a]+degree[b]);lead.append(lead[a]*lead[b]%p);height.append(height[a]+height[b])
            else:
                z=max(degree[a],degree[b]);degree.append(z)
                x=lead[a] if degree[a]==z else 0;y=lead[b] if degree[b]==z else 0
                lead.append((x+y if op=='+' else x-y)%p);height.append(max(height[a],height[b])+1)
    bounds=[degree[r] for r in d['residual_roots']]
    need(bounds==dc['residual_degree_bounds'],'Degree bounds')
    need(dc['degree']==2*max(bounds),'Degree maximum')
    w=dc['witness_residual'];r=d['residual_roots'][w]
    need(bounds[w]==max(bounds) and lead[r]!=0 and lead[r]==dc['witness_top_residue'],'Top homogeneous witness')
    hb=max(2*height[r] for r in d['residual_roots'])+(len(bounds)-1).bit_length()
    need(hb==dc['coefficient_height_at_most_power_of_two'],'Height bound')
    dep=d['dependency_certificate'];need(dep['modulus']==p,'Dependency prime')
    point=dep['point'];need(len(point)==len(inds),'Dependency point length')
    vals=[];deriv=[]
    # Forward automatic differentiation is independent of producer reverse mode.
    for n in d['nodes']:
        op=n[0]
        if op=='const':a=n[1]%p;da=[0]*len(inds)
        elif op=='var':a=point[n[1]]%p;da=[0]*len(inds);da[n[1]]=1
        else:
            i,j=n[1:]
            if op=='*':a=vals[i]*vals[j]%p;da=[(x*vals[j]+y*vals[i])%p for x,y in zip(deriv[i],deriv[j])]
            else:
                sign=1 if op=='+' else -1;a=(vals[i]+sign*vals[j])%p
                da=[(x+sign*y)%p for x,y in zip(deriv[i],deriv[j])]
        vals.append(a);deriv.append(da)
    grad=deriv[d['output']];need(all(grad) and grad==dep['gradient'],'Actual input dependence')
    live=set()
    def visit(i):
        if i in live:return
        live.add(i);n=d['nodes'][i]
        if n[0] in ('+','-','*'):visit(n[1]);visit(n[2])
    visit(d['output'])
    metrics={'variables':len(inds),'residuals':len(bounds),'degree':dc['degree'],
        'live_binary_operations':sum(d['nodes'][i][0] in ('+','-','*') for i in live),
        'maximum_literal_absolute_value':max(abs(d['nodes'][i][1]) for i in live if d['nodes'][i][0]=='const'),
        'coefficient_height_bound_exponent':hb}
    need(metrics==d['metrics'],'Metric mismatch')
    return {'metrics':metrics,'fused_residual_terms':len(expected),'semantic_ports':len(required)}

def main():
    source=json.loads((ROOT/'sources/anchor219.json').read_text());receipts=[];controls=0
    for path in sorted((ROOT/'equations').glob('integer*_degree*.json')):
        d=json.loads(path.read_text());pp=ROOT/'sources'/d['parent_file']
        need(sha(pp)==d['parent_sha256'],'Parent byte binding')
        parent=json.loads(pp.read_text())
        need(parent['source219_sha256']==sha(ROOT/'sources/anchor219.json'),'Source byte binding')
        receipt=check(d,parent,source)
        mutants=[]
        bad=copy.deepcopy(d);bad['degree_certificate']['degree']+=2;mutants.append(bad)
        bad=copy.deepcopy(d);bad['residual_roots'][0]=bad['residual_roots'][1];mutants.append(bad)
        bad=copy.deepcopy(d);bad['source_value_nodes']['126']=bad['source_value_nodes']['184'];mutants.append(bad)
        bad=copy.deepcopy(d);bad['deleted_source_indices']=[209,210,211];mutants.append(bad)
        bad=copy.deepcopy(d);r=bad['residual_roots'][-1];bad['nodes'][r][0]='+';mutants.append(bad)
        for bad in mutants:
            try:check(bad,parent,source)
            except (ValueError,KeyError,IndexError):controls+=1
            else:raise ValueError('Corrupted certificate accepted')
        receipts.append({'file':path.name,'sha256':sha(path),**receipt})
    out={'status':'pass','profiles':receipts,'corruptions_rejected':controls,
         'scope':'Finite source identities, private guard binding, exact circuit changes, degree, height bound, input dependence; unbounded completeness is the separate proof.'}
    print(json.dumps(out,sort_keys=True,indent=2))
if __name__=='__main__':main()
