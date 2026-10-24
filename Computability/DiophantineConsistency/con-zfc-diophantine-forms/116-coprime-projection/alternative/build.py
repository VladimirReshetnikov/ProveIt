#!/usr/bin/env python3
"""Emit literal ordinary polynomial DAGs. No variable exponent operation exists."""
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'prior'))
from build_dag import Ring, make
from core import CORNERS


def power_graph(ring, requests, prefix='p_', retain_A=False):
    c, add, mul, sub, pw = ring.c, ring.add, ring.mul, ring.sub, ring.pow
    z, U, v, q, b = [ring.v(prefix + name) for name in ('z','U','v','q','b')]
    locals_ = [[ring.v(prefix + name + str(i)) for name in ('y','h','s','t')]
               for i in range(len(requests))]
    Ys = [add(k, row[0]) for (n,k,m), row in zip(requests,locals_)]
    D = mul(*Ys)
    V = mul(pw(D,2),add(v,c(1)))
    B = add(c(1),mul(c(4),D,add(q,c(1))))
    A = ring.v(prefix + 'A') if retain_A else sub(B,mul(U,b))
    W = add(c(2), *(x for req in requests for x in req))
    def norm(a,x,y):
        return sub(sub(pw(x,2),mul(sub(pw(a,2),c(1)),pw(y,2))),c(1))
    rows = {
        'scale': sub(sub(pw(A,2),mul(pw(W,3),add(W,c(2)),pw(add(z,c(1)),2))),c(1)),
        'auxiliary_norm': norm(A,U,V),
    }
    if retain_A:
        rows['base_congruence'] = sub(sub(B,A),mul(U,b))
    out = {'A':A,'B':B,'D':D,'V':V,'W':W}
    for i, ((n,k,m),(y,h,s,t),Y) in enumerate(zip(requests,locals_,Ys)):
        T = sub(sub(mul(c(2),A,n),pw(n,2)),c(1))
        X = add(mul(Y,sub(A,n)),m,mul(T,h))
        S = add(X,mul(U,s))
        R = add(k,mul(c(4),Y,t))
        rows['main_norm_'+str(i)] = norm(A,X,Y)
        rows['index_norm_'+str(i)] = norm(B,S,R)
        out.update({name+str(i):value for name,value in [('Y',Y),('T',T),('X',X),('S',S),('R',R)]})
    return rows, out


def live_nodes(ring, root):
    live=set()
    def visit(i):
        if i in live: return
        live.add(i)
        node=ring.nodes[i]
        if node['op'] in ('add','mul'):
            for j in node['args']: visit(j)
        elif node['op']=='pow_fixed': visit(node['base'])
    visit(root)
    return live


def finish(ring, rows, out, name, inputs, details):
    polynomial=ring.add(*(ring.pow(x,2) for x in rows.values()))
    live=live_nodes(ring,polynomial)
    variables=sorted({ring.nodes[i]['name'] for i in live if ring.nodes[i]['op']=='var'})
    binary_ops=0
    for i in live:
        node=ring.nodes[i]
        if node['op'] in ('add','mul'):
            binary_ops+=max(0,len(node['args'])-1)
        elif node['op']=='pow_fixed':
            e=node['exponent']
            binary_ops+=0 if e<=1 else e.bit_length()+e.bit_count()-2
    return {
        'format':'ordinary-integer-polynomial-dag-v1',
        'name':name,
        'ordinary_polynomial_claim':True,
        'domain':'nonnegative integers',
        'nodes':ring.nodes,
        'residuals':rows,
        'output':polynomial,
        'defined_ports':out,
        'inputs':inputs,
        'variables':variables,
        'variable_count':len(variables),
        'auxiliary_count':len(variables)-len(inputs),
        'residual_count':len(rows),
        'live_nodes':len(live),
        'binary_operations_upper_bound_with_per_node_binary_powering':binary_ops,
        'degree_upper_bound':ring.degrees[polynomial],
        'residual_degree_upper_bounds':{name:ring.degrees[idx] for name,idx in rows.items()},
        'special_function_graphs':[],
        **details,
    }


def generic(r,retain_A=False):
    ring=Ring()
    requests=[tuple(ring.v(n+str(i)) for n in ('n','k','m')) for i in range(r)]
    rows,out=power_graph(ring,requests,retain_A=retain_A)
    inputs=[n+str(i) for i in range(r) for n in ('n','k','m')]
    return finish(ring,rows,out,'simultaneous_positive_powers_'+str(r)+('_retained' if retain_A else ''),inputs,
                  {'request_count':r,'input_restrictions':'n_i >= 1, k_i >= 1, m_i >= 0',
                   'exact_degree':None if retain_A else 12*r+8,
                   'theorem':'All m_i=n_i^k_i iff natural auxiliary zero exists.'})


def tiling(tiles,retain_A=False):
    ring,out,constants=make(tiles,shift=True)
    c,add,mul,sub=ring.c,ring.add,ring.mul,ring.sub
    P,A,Y=[out[n] for n in ('P','A','Y')]
    n=mul(add(A,c(1)),Y)
    v,q,u,t,j=[ring.v(name) for name in ('v0','q0','u','t','j')]
    d=mul(P,add(n,v,c(1)))
    e=mul(d,add(u,t,c(1)))
    W0=add(mul(e,add(mul(c(2),q),c(1))),mul(d,u),c(1))
    S=sub(sub(e,c(1)),mul(sub(d,c(1)),add(Y,mul(sub(d,c(1)),j))))
    requests=[(c(2),n,e),(add(d,c(1)),A,W0)]
    rows,pg=power_graph(ring,requests,retain_A=retain_A)
    rows['synchronization']=S
    out.update(n=n,d=d,e=e,W0=W0,S=S)
    out.update({'pell_'+k:v for k,v in pg.items()})
    return finish(ring,rows,out,'four_corner_tiling_'+('22' if retain_A else '21'),[],
                  {'tiles':[tile.__dict__ for tile in tiles],'constants':constants,
                   'theorem':'Zero iff this fixed tile set has a finite strict-boundary rectangular tiling.',
                   'consistency_endpoint_claim':False,
                   'remaining_obligation':'Supply and calibrate a strict-boundary ZFC-proof-checker tile set.',
                   'uniform_k_tile_degree_bound':(1152 if retain_A else 1728)*len(tiles)+8})


def products():
    return {
        'POWER_ONE_9AUX.json':generic(1),
        'POWER_TWO_13AUX.json':generic(2),
        'POWER_TWO_14AUX.json':generic(2,True),
        'FOUR_CORNER_21NAT.json':tiling(CORNERS),
        'FOUR_CORNER_22NAT.json':tiling(CORNERS,True),
    }


def main():
    check='--check' in sys.argv
    summary={}
    for filename,obj in products().items():
        raw=(json.dumps(obj,indent=2)+'\n').encode()
        path=HERE/filename
        if check:
            if not path.exists() or path.read_bytes()!=raw:
                raise RuntimeError('Rebuild mismatch: '+filename)
        else: path.write_bytes(raw)
        summary[filename]={k:obj[k] for k in ['variable_count','auxiliary_count','residual_count','degree_upper_bound','live_nodes','binary_operations_upper_bound_with_per_node_binary_powering']}
        summary[filename]['sha256']=hashlib.sha256(raw).hexdigest()
    if not check:
        (HERE/'METRICS.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({'status':'PASS','rebuild_check':check,'artifacts':summary},indent=2))


if __name__=='__main__': main()
