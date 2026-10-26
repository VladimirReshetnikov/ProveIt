#!/usr/bin/env python3
"""Build explicit fixed polynomials by reciprocal pooling across all bases.

Python's standard library suffices. The input equation and independently
audited interface are literal data. No search for a ZFC refutation occurs.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def canonical(x):
    return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def parse(terms):
    return {tuple(m):c for c,m in terms}
def serial(p):
    return [[c,list(m)] for m,c in sorted(p.items()) if c]
def add(*ps):
    out={}
    for p in ps:
        for m,c in p.items(): out[m]=out.get(m,0)+c
    return {m:c for m,c in out.items() if c}
def scale(c,p): return {m:c*v for m,v in p.items() if c*v}
def neg(p): return scale(-1,p)
def sub(p,q): return add(p,neg(q))
def mul(p,q):
    out={}
    for m,c in p.items():
        for n,d in q.items():
            k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
    return {m:c for m,c in out.items() if c}
def sq(p): return mul(p,p)
def remap(p,mp): return {tuple(sorted(mp[i] for i in m)):c for m,c in p.items()}

class Circuit:
    """Hash-consed straight-line program using integer leaves and +,-,*."""
    def __init__(self): self.nodes=[];self.cache={}
    def node(self,*v):
        if v in self.cache:return self.cache[v]
        i=len(self.nodes);self.cache[v]=i;self.nodes.append(list(v));return i
    def const(self,c):return self.node('const',c)
    def var(self,i):return self.node('var',i)
    def op(self,op,a,b):return self.node(op,a,b)
    def plus(self,a,b):return self.op('+',a,b)
    def minus(self,a,b):return self.op('-',a,b)
    def times(self,a,b):return self.op('*',a,b)
    def square(self,a):return self.times(a,a)
    def sum(self,ls):
        if not ls:return self.const(0)
        r=ls[0]
        for x in ls[1:]:r=self.plus(r,x)
        return r
    def product(self,ls):
        if not ls:return self.const(1)
        r=ls[0]
        for x in ls[1:]:r=self.times(r,x)
        return r
    def poly(self,p):
        parts=[]
        for m,c in sorted(p.items()):
            a=self.product([self.var(i) for i in m])
            if c!=1:a=self.times(self.const(c),a)
            parts.append(a)
        return self.sum(parts)
    def compact(self,outputs):
        live=set()
        def visit(i):
            if i in live:return
            live.add(i);n=self.nodes[i]
            if n[0] in ('+','-','*'):visit(n[1]);visit(n[2])
        for i in outputs:visit(i)
        order=sorted(live);mp={old:new for new,old in enumerate(order)}
        ns=[]
        for i in order:
            n=list(self.nodes[i])
            if n[0] in ('+','-','*'):n=[n[0],mp[n[1]],mp[n[2]]]
            ns.append(n)
        return ns,[mp[i] for i in outputs]

def make_circuit(eq):
    c=Circuit()
    quadratic=[c.poly(parse(r['terms'])) for r in eq['quadratic_residuals']]
    ns=[c.poly(parse(b['base'])) for b in eq['blocks']]
    ts=[c.poly(parse(b['T'])) for b in eq['blocks']]
    es=[]
    for b in eq['blocks']:
        es.append(c.minus(c.poly(parse(b['S'])),c.times(c.times(c.const(2),c.poly(parse(b['base']))),c.poly(parse(b['H'])))))
    pools=[]
    for p in eq['pools']:
        ids=p['blocks']
        summands=[c.product([es[j]]+[ts[h] for h in ids if h!=j]) for j in ids]
        pools.append(c.minus(c.sum(summands),c.product([c.var(p['z'])]+[ts[h] for h in ids])))
    res=quadratic+pools
    out=c.sum([c.square(a) for a in res])
    nodes,outputs=c.compact(res+[out])
    return {'schema':'integer-polynomial-circuit-v1','domain':'unrestricted integers',
            'variables':eq['variables'],'nodes':nodes,'residual_outputs':outputs[:-1],
            'output':outputs[-1],
            'leaf_convention':'var index refers to the zero-based variables array; const is an exact integer; binary nodes refer only to earlier nodes'}

def degree_witness(circuit,point):
    """An upper bound plus exact leading-form evaluation at one point."""
    ds=[];ls=[]
    for n in circuit['nodes']:
        if n[0]=='const':d=0;l=n[1]
        elif n[0]=='var':d=1;l=point.get(n[1],0)
        else:
            op,a,b=n
            if op=='*':d=ds[a]+ds[b];l=ls[a]*ls[b]
            else:
                d=max(ds[a],ds[b]);l=(ls[a] if ds[a]==d else 0)+(1 if op=='+' else -1)*(ls[b] if ds[b]==d else 0)
        ds.append(d);ls.append(l)
    return {'upper_degree':ds[circuit['output']],'leading_value':ls[circuit['output']],
            'point':{str(k):v for k,v in sorted(point.items()) if v},
            'residual_degrees':[ds[i] for i in circuit['residual_outputs']],
            'residual_leading_values':[ls[i] for i in circuit['residual_outputs']]}

def height_bound_bits(circuit):
    """If B is returned, the expanded coefficient height is strictly <2^B."""
    norms=[]
    for n in circuit['nodes']:
        if n[0]=='const':a=abs(n[1])
        elif n[0]=='var':a=1
        elif n[0]=='*':a=norms[n[1]]*norms[n[2]]
        else:a=norms[n[1]]+norms[n[2]]
        norms.append(a)
    return norms[circuit['output']].bit_length()

def build(partition):
    parent=json.loads((ROOT/'inputs/source216.json').read_text())
    interface=json.loads((ROOT/'inputs/interface216.json').read_text())
    actual=hashlib.sha256((ROOT/'inputs/source216.json').read_bytes()).hexdigest()
    if actual!=interface['source_sha256']:raise ValueError('Source hash mismatch')
    retained=interface['retained_variables'];mp={old:new for new,old in enumerate(retained)}
    reqs={r['request']:r for r in interface['requests']}
    blocks=[]
    for b in interface['blocks']:
        ps=[reqs[i] for i in b['requests']]
        H=add(*(mul(parse(r['Y']),sub(parse(r['m']),parse(r['X']))) for r in ps))
        S=add(*(sub(sq(sub(parse(r['m']),parse(r['D']))),sq(parse(r['Y']))) for r in ps))
        E=sub(S,scale(2,mul(parse(b['base']),H)))
        vals={'base':parse(b['base']),'T':parse(b['T']),'H':H,'S':S,'E':E}
        blocks.append({'name':b['name'],'requests':b['requests'],**{k:serial(remap(v,mp)) for k,v in vals.items()}})
    variables=[{**parent['variables'][i],'source_index':i} for i in retained]
    pools=[]
    if sorted(j for p in partition for j in p)!=list(range(5)):raise ValueError('Invalid partition')
    for i,p in enumerate(partition):
        pools.append({'blocks':p,'z':len(variables)})
        variables.append({'name':f'mixed_pool.z{i}','kind':'unrestricted integer'})
    eq={'schema':'conzfc-mixed-pooling-v1','domain':'unrestricted integers','pooling_mode':'unweighted',
        'definition':'sum of squares of all quadratic_residuals and all pools; pool R=sum_j E_j*product_(h!=j)T_h-z*product_h T_h; E_j=S_j-2*base_j*H_j',
        'source_sha256':actual,'variables':variables,
        'quadratic_residuals':[{'source_row':i,'label':parent['residuals'][i]['label'],
                               'terms':serial(remap(parse(parent['residuals'][i]['terms']),mp))} for i in interface['retained_rows']],
        'A':serial(remap(parse(interface['A']),mp)),
        'blocks':blocks,'pools':pools,
        'requests':[{**{k:v for k,v in r.items() if k in ('request','pair')},
                     **{k:serial(remap(parse(v),mp)) for k,v in r.items() if k not in ('request','pair')}} for r in interface['requests']],
        'source_to_output':{str(old):new for old,new in mp.items()}}
    circ=make_circuit(eq)
    # A sparse exact point certifies nonvanishing of the top homogeneous form.
    # For the selected partitions singleton0 is in a largest block.
    oldpoint={0:1,3:1,4:1,138:1,185:1,209:1}
    point={mp[k]:v for k,v in oldpoint.items()}
    for p in pools:point[p['z']]=1
    dw=degree_witness(circ,point)
    if not dw['leading_value']:raise ValueError('Degree witness cancels')
    n=len(variables);deg=dw['upper_degree']
    used={v[1] for v in circ['nodes'] if v[0]=='var'}
    if used!=set(range(n)):raise ValueError('Unused coordinate')
    metrics={'variables':n,'residuals':len(circ['residual_outputs']),
             'retained_quadratic_residuals':len(eq['quadratic_residuals']),
             'new_pool_residuals':len(pools),'exact_total_degree':deg,
             'binary_operations':sum(n[0] in ('+','-','*') for n in circ['nodes']),
             'maximum_literal_integer':max(abs(n[1]) for n in circ['nodes'] if n[0]=='const'),
             'all_coordinates_syntactically_used':True,
             'expanded_coefficient_height':'not computed','expanded_support':'not computed',
             'coefficient_height_strictly_less_than_2_power':height_bound_bits(circ),
             'degree_certificate':dw}
    cert={'source_sha256':actual,'removed_rows':interface['deleted_rows'],
          'removed_variables':interface['deleted_variables'],
          'retained_rows':interface['retained_rows'],'retained_variables':retained,
          'partition':partition,'result_sha256':hashlib.sha256(canonical(eq)).hexdigest(),
          'source_interface':'inputs/interface216.json',
          'forward':'For each pool, z=sum E_j/T_j. On source zeros all quotients are integers.',
          'backward':'Use mixed-sign reciprocal pooling theorem. Singleton: restore T=2An-n^2-1, Q=-(m-D-nY)/T. Existing pool: restore L=E/T and K=2H+(2A-n)L.'}
    return f'integer{n}_degree{deg}',eq,circ,metrics,cert

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=ROOT/'equations');args=ap.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    summaries=[]
    for partition in [[[0,1,2,3,4]],[[0,1,2],[3,4]],[[0,1],[2,3],[4]],[[0],[1],[2],[3],[4]]]:
        name,eq,circ,metrics,cert=build(partition);dest=args.output/name;dest.mkdir(exist_ok=True)
        for fn,obj in [('equation.json',eq),('circuit.json',circ),('METRICS.json',metrics),('certificate.json',cert)]:
            (dest/fn).write_bytes(canonical(obj))
        summaries.append({k:v for k,v in metrics.items() if k!='degree_certificate'})
    print(json.dumps(summaries,indent=2,sort_keys=True))

if __name__=='__main__':main()
