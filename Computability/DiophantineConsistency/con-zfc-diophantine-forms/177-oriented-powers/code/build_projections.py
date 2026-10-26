#!/usr/bin/env python3
"""Emit finite polynomial circuits from frozen acyclic unit-pivot certificates.

The monic-elimination method follows ProveIt package 152. The implementation
here retains the factored oriented-pool expressions, avoiding their expansion
inside the final circuits. No search is needed to reproduce the artifacts.
"""
import argparse, hashlib, json, math
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
PRIME=1000000007
def encoded(x): return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def load(path): return json.loads(Path(path).read_text())

def build(source, pool, profile, source_hash):
    n=len(source['variables']); rows=source['residuals']; defs={}; removed=set()
    for step in profile['steps']:
        r,v=step['row'],step['variable']
        if r in removed or v in defs: raise ValueError('duplicate pivot')
        terms=rows[r]['terms']; cs=[c for c,m in terms if m==[v]]
        if len(cs)!=1 or abs(cs[0])!=1 or any(v in m for c,m in terms if m!=[v]):
            raise ValueError('pivot is not a unit-linear definition')
        defs[v]=(r,[[-cs[0]*c,m] for c,m in terms if m!=[v]])
        removed.add(r)
    inputs=[v for v in range(n) if v not in defs]
    nodes=[['var',i] for i in range(len(inputs))]; roots=dict(zip(inputs,range(len(inputs))))
    deg={v:1 for v in inputs}; norm={v:1 for v in inputs}; top={v:(v+3)%PRIME for v in inputs}
    blocks=[]; visiting=set()
    def node(op,*args): nodes.append([op,*args]); return len(nodes)-1
    def expression(terms,registers):
        start=len(nodes)
        def term(c,m):
            if not m:return node('const',abs(c))
            value=registers[m[0]]
            for j in m[1:]:value=node('*',value,registers[j])
            if abs(c)!=1:value=node('*',node('const',abs(c)),value)
            return value
        def total(vs):
            if not vs:return None
            val=vs[0]
            for q in vs[1:]:val=node('+',val,q)
            return val
        pos=total([term(c,m) for c,m in terms if c>0]); neg=total([term(c,m) for c,m in terms if c<0])
        if pos is None:out=node('-',node('const',0),neg) if neg is not None else node('const',0)
        elif neg is None:out=pos
        else:out=node('-',pos,neg)
        if out<start:out=node('+',out,node('const',0))
        return start,out
    def bounds(terms):
        d=max((sum(deg[j] for j in m) for c,m in terms),default=0)
        b=sum(abs(c)*math.prod(norm[j] for j in m) for c,m in terms)
        t=sum(c*math.prod(top[j] for j in m) for c,m in terms if sum(deg[j] for j in m)==d)%PRIME
        return d,b,t
    def define(v):
        if v in roots:return
        if v in visiting:raise ValueError('cyclic definitions')
        visiting.add(v);r,terms=defs[v]
        for c,m in terms:
            for j in m:define(j)
        start,end=expression(terms,roots);deg[v],norm[v],top[v]=bounds(terms)
        roots[v]=end;blocks.append(dict(kind='definition',source_row=r,variable=v,start=start,root=end));visiting.remove(v)
    for v in sorted(defs):define(v)
    pool_start=len(rows)-len(pool['blocks']); residual_roots=[]; kept=[]; rd=[]; rn=[]; rt=[]
    def retain(r,kind='residual',formal=None,registers=None,extra=None):
        if r in removed:return
        start,end=expression(rows[r]['terms'] if formal is None else formal,roots if registers is None else registers)
        block=dict(kind=kind,source_row=r,start=start,root=end)
        if extra:block.update(extra)
        blocks.append(block);kept.append(r);residual_roots.append(end)
        d,b,t=bounds(rows[r]['terms']);rd.append(d);rn.append(b);rt.append(t)
    for r in range(pool_start):retain(r)
    macro_regs={}; macro_ids={}; next_id=n
    for gi,g in enumerate(pool['groups']):
        for field in ('base','T','E','delta'):
            if field not in g:continue
            start,end=expression(g[field],roots);ident=next_id;next_id+=1
            macro_ids[(gi,field)]=ident;macro_regs[ident]=end
            blocks.append(dict(kind='macro',group=gi,field=field,formal_index=ident,start=start,root=end))
    for bi,b in enumerate(pool['blocks']):
        r=pool_start+bi
        if r in removed:continue
        gs=b['groups'];z=b['quotient_index']; Ts=[macro_ids[(j,'T')] for j in gs]
        if b['weights']=='direct':terms=[[1,[macro_ids[(gs[0],'delta')]]],[1,[z,Ts[0]]]]
        else:
            terms=[[-1,[z]+Ts]]
            for at,j in enumerate(gs):
                mon=([macro_ids[(j,'base')]] if b['weights']=='base' else [])+[macro_ids[(j,'E')]]+[t for k,t in enumerate(Ts) if k!=at]
                terms.append([1,mon])
        retain(r,'pool',terms,{**roots,**macro_regs},dict(pool_block=bi))
    start=len(nodes);squares=[node('*',r,r) for r in residual_roots];out=squares[0]
    for r in squares[1:]:out=node('+',out,r)
    blocks.append(dict(kind='sum_of_squares',start=start,root=out))
    D=max(rd);w=next((i for i,d in enumerate(rd) if d==D and rt[i]!=0),None)
    if w is None:raise ValueError('chosen leading specialization did not certify the degree')
    live=set();todo=[out]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i)
        if nodes[i][0] in ('+','-','*'):todo.extend(nodes[i][1:])
    metrics=dict(variables=len(inputs),residuals=len(kept),degree=2*D,
        eliminated_variables=len(defs),coefficient_height_strict_power_of_two=sum(x*x for x in rn).bit_length(),
        binary_operations=sum(nodes[i][0] in ('+','-','*') for i in live),
        maximum_literal_constant=max(abs(nodes[i][1]) for i in live if nodes[i][0]=='const'),stored_nodes=len(nodes))
    return dict(schema='oriented-acyclic-polynomial-v1',domain='unrestricted integers',variant=profile['variant'],
        source_sha256=source_hash,retained_source_indices=inputs,
        variables=[dict(source_index=v,**source['variables'][v]) for v in inputs],nodes=nodes,blocks=blocks,
        residual_roots=residual_roots,output=out,metrics=metrics,
        degree_certificate=dict(source_degrees=[deg[i] for i in range(n)],retained_rows=kept,residual_degrees=rd,
        modulus=PRIME,input_direction='source_index + 3',witness_source_row=kept[w],witness_top_residue=rt[w]))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');ap.add_argument('--output',type=Path);a=ap.parse_args()
    results=[]
    for path in sorted((ROOT/'certificates').glob('*.json')):
        p=load(path); base=ROOT/'sources'/p['variant']; raw=(base/'equation.json').read_bytes()
        result=build(json.loads(raw),load(base/'certificate.json'),p,hashlib.sha256(raw).hexdigest())
        name='integer%d_degree%d'%(result['metrics']['variables'],result['metrics']['degree'])
        if name!=path.stem:raise ValueError('certificate filename does not match computed result: '+name)
        data=encoded(result);dest=(a.output or ROOT/'equations')/(name+'.json')
        if a.check:
            if dest.read_bytes()!=data:raise ValueError('rebuild mismatch: '+name)
        else:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
        results.append(dict(name=name,**result['metrics']))
    print(json.dumps(dict(status='PASS',profiles=results),indent=2))
if __name__=='__main__':main()
