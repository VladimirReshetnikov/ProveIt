#!/usr/bin/env python3
"""Three-root scalar carriers from coprime Pell saturation, over Z^12."""
import argparse
import ast
from collections import Counter
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
VARS = ['j','C','z','h','r','v','w','T','c','n','t','s']
PORTS = ['beta','K0','MC','MF','cone_A','cone_B']
PREFIX = [
 ('J','6*j+1'),('qm','beta*J'),('q','qm+1'),('q2','q*q'),('q3','q2*q'),
 ('W0','12*w+4'),('X','q*W0'),('Y','(2*v+1)*q3'),('XY','X*Y'),('a','XY+Y'),
 ('H','4*a+3'),('Delta','a*a+H'),('F','(K0+W0)*C-z*qm'),
 ('R','(q*(q-F)-C)*(q2-1)+(MC+q*MF)*J'),('k','R+1+h*XY'),
 ('eta','c-Y*k'),('zeta','k-eta'),('coneU','cone_A*F'),('coneV','cone_B*C'),
 ('G','coneU*coneV-(q-coneU-coneV)*(q-coneU-coneV)'),('Peta','eta*zeta'),
 ('err','t*t-G-Peta+1'),('Pair','G*Peta-err*err'),('Dg81','(243*Pair-324)*s*s+81'),
 ('ell','X*Y*Y'),('ellk','ell*k'),('Dt','ellk*(ellk+k)+1'),
 ('c2','c*c'),('U','s*r*c2'),('UDt','U*Dt'),('strong','Delta*U*UDt'),
 ('Df','strong+1'),('Q','Delta*strong'),('delta','Q-1'),
 ('b','c-R+4*UDt*T'),('V','Df*b-c'),('Cy','Q*V*V-1'),
 ('K','X*(X+2*a*c)-1'),('H2','H*H'),('H3','H2*H'),('H5','H2*H3'),
 ('S','U*H5'),('S2','S*S'),('zc','H*T+K'),('zc2','zc*zc'),('zc3','zc2*zc'),
 ('Ac','(zc2+3*H2)*(zc3-19*H3)'),('G2','Dt*Df')]


class DAG:
    def __init__(self):
        self.nodes=[]
        self.memo={}

    def emit(self,row):
        key=tuple(row)
        if key not in self.memo:
            self.memo[key]=len(self.nodes)
            self.nodes.append(list(row))
        return self.memo[key]

    def op(self,op,a,b):
        left,right=self.nodes[a],self.nodes[b]
        if left[0]==right[0]=='integer':
            x,y=left[1],right[1]
            return self.emit(['integer',x+y if op=='add' else x-y if op=='sub' else x*y])
        if op=='mul':
            if left==['integer',1]:return b
            if right==['integer',1]:return a
        if op in ['add','mul'] and a>b:a,b=b,a
        return self.emit([op,a,b])

    def expression(self,text,env):
        def visit(n):
            if isinstance(n,ast.Name):return env[n.id]
            if isinstance(n,ast.Constant):return self.emit(['integer',n.value])
            if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):
                return self.op('sub',self.emit(['integer',0]),visit(n.operand))
            if isinstance(n,ast.BinOp):
                return self.op({ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul'}[type(n.op)],visit(n.left),visit(n.right))
            raise ValueError('nonpolynomial syntax')
        return visit(ast.parse(text,mode='eval').body)


def circuit(integral=False):
    d=DAG()
    env={v:d.emit(['variable',v]) for v in VARS}
    env.update({p:d.emit(['coefficient',p]) for p in PORTS})
    formulas=list(PREFIX)
    if integral:
        formulas += [('center','S*(n+delta*V)-Ac'),('scale','S2'),('fc','S2*delta*Cy'),('fs','center*center')]
    else:
        formulas += [('center','S*(n+V)-Ac'),('scale','delta*S2'),('fc','S2*Cy'),('fs','delta*center*center')]
    formulas += [('fa','9*scale*G2'),('fb','scale*Dg81'),
                 ('sum','fs+fc'),('ab','fa+fb'),('Po','sum-ab'),
                 ('sc','fs*fc'),('aXb','fa*fb'),('scab','sc+aXb'),
                 ('Pe','Po*Po-4*scab'),('product','sc*aXb'),
                 ('output','Pe*Pe-64*product')]
    for name,text in formulas:env[name]=d.expression(text,env)
    live=set();todo=[env['output']]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i)
        if d.nodes[i][0] in ['add','sub','mul']:todo.extend(d.nodes[i][1:])
    order=sorted(live);mapping={i:j for j,i in enumerate(order)}
    nodes=[[r[0],mapping[r[1]],mapping[r[2]]] if r[0] in ['add','sub','mul'] else r
           for i in order for r in [d.nodes[i]]]
    names={v:mapping[i] for v,i in env.items() if i in live}
    counts=dict(Counter(r[0] for r in nodes if r[0] in ['add','sub','mul']))
    deg=[]
    for r in nodes:
        deg.append((deg[r[1]]+deg[r[2]] if r[0]=='mul' else max(deg[r[1]],deg[r[2]]))
                   if r[0] in ['add','sub','mul'] else int(r[0]=='variable'))
    return dict(schema='literal_integer_arithmetic_dag_v1',
                name='saturated_scalar12_'+('integral' if integral else 'rational'),
                variant='integral' if integral else 'rational', domain='unrestricted integers',
                variables=VARS,variable_count=12,nodes=nodes,named_registers=names,output=names['output'],
                operations=sum(counts.values()),operation_counts=counts,
                coefficient_binding='coefficients/BINDING.json',
                exact_degree=1280 if integral else 1084,syntactic_bound=deg[names['output']],
                proof='PROOF.md',source_commit='84e16e43092614bae262ca59651cb9d77e31a255',
                proof_status='New ordinary arithmetic reduction via coprime saturation, '
                             'three-adic root separation and full-residue interpolation. '
                             'Named parent native/refutation calibration is inherited; no new Lean endpoint.')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check',action='store_true')
    args=ap.parse_args();results={}
    for integral in [False,True]:
        packet=circuit(integral);variant=packet['variant']
        raw=(json.dumps(packet,indent=2,sort_keys=True)+'\n').encode()
        path=HERE/(variant+'.json')
        if args.check:
            if path.read_bytes()!=raw:raise ValueError('deterministic rebuild '+variant)
        else:path.write_bytes(raw)
        results[variant]={k:packet[k] for k in ['operations','operation_counts','exact_degree','syntactic_bound']}
    print(json.dumps(dict(status='PASS',check=args.check,variants=results),indent=2))


if __name__=='__main__':main()
