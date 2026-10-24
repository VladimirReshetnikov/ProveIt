#!/usr/bin/env python3
"""Exact literal DAGs for CRT quotient fusion; standard library only."""
from pathlib import Path
import hashlib, json

ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
EXPORTED_VARIANTS=((20,False),(20,True),(19,True),(18,True))
COMMON=['J3','F','alpha','z','f','h','r','v_scale','w3','tau','eta','y','gamma','T']
GUARD=['pair_root','pair_pos1','pair_pos2','pair_pos3']

class DAG:
    def __init__(self, variables):
        self.nodes=[]; self.index={};self.variables=variables
    def intern(self, tag, *args):
        key=(tag,*args)
        if key not in self.index:
            self.index[key]=len(self.nodes);self.nodes.append([tag,*args])
        return Expr(self,self.index[key])
    def coerce(self,x):
        if isinstance(x,Expr):return x
        return self.intern('constant',x)
    def op(self,op,a,b):
        a,b=self.coerce(a),self.coerce(b)
        if op in ('add','mul') and a.i>b.i:a,b=b,a
        return self.intern(op,a.i,b.i)
class Expr:
    def __init__(self,d,i):self.d,self.i=d,i
    def __add__(self,b):return self.d.op('add',self,b)
    def __radd__(self,b):return self.d.op('add',b,self)
    def __sub__(self,b):return self.d.op('sub',self,b)
    def __rsub__(self,b):return self.d.op('sub',b,self)
    def __mul__(self,b):return self.d.op('mul',self,b)
    def __rmul__(self,b):return self.d.op('mul',b,self)
    def __pow__(self,n):
        if n==0:return self.d.coerce(1)
        if n==1:return self
        if n%2==0:
            a=self**(n//2);return a*a
        return self*(self**(n-1))

def make(variant, transport=False):
    variables=COMMON+(['a','c'] if variant==20 else ['c'])+GUARD
    if variant==18:variables.remove('eta')
    if transport:
        variables.remove('F');variables.remove('alpha');variables.insert(1,'C')
    d=DAG(variables)
    v={x:d.intern('variable',x) for x in variables}
    p={x:d.intern('port',x) for x in PORTS}
    J=3*v['J3']+1; q=p['beta']*J+1; W=4*(3*v['w3']+1)
    X=q*W; Y=(2*v['v_scale']+1)*q**3
    if transport:
        C=v['C'];F=(p['K0']+W)*C-v['z']*(q-1);alpha=q-F-C
    else:
        F=v['F'];alpha=v['alpha'];C=q-F-alpha
    c=v['c'];f=v['f'];h=v['h'];y=v['y']
    E=v['a']-Y if variant==20 else X*Y
    a=v['a'] if variant==20 else E+Y
    H=4*a+3; delta=a*a+H
    R=((q*(q-F)-C) if transport else ((q-1)*(q-F)+alpha))*(q*q-1)+(p['MC']+q*p['MF'])*J
    k=R+1+h*E
    eta=v['eta'] if variant!=18 else c-Y*k
    zeta=k-eta
    cT=c*v['T']; f2=f*f; B=f2*(cT-R); V=B-c
    I=(2*v['r']+1)*c*c; I2=I*I;Q=delta*(f2-1)
    Z=eta*zeta;U=p['cone_A']*F;VV=p['cone_B']*C
    G=U*VV-(q-U-VV)**2
    Pos=1+v['pair_pos1']**2+v['pair_pos2']**2+v['pair_pos3']*(v['pair_pos3']+1)
    b=E*(c-eta)
    main=(X+a*c+v['gamma']*H)**2-delta*c*c-1
    aux=(B+y)**2-(Q if variant==20 else I2)*(c+y)*(2*B+y-c)-1
    rows={}
    if variant==20:rows['scale']=a-(X+1)*Y
    if variant!=18:rows['remainder']=c-eta-Y*k
    rows.update({
      'first_norm':v['tau']**2+(2*v['tau']-k)*b-1,
      'main_norm':main,
      'strong_norm':I2-Q,
      'auxiliary_norm':aux,
      'joint_guard':G*Z-(v['pair_root']**2-G-Z+1)**2-Pos
    })
    if not transport:
        rows=dict(list(rows.items())[:4]+[('transport',(p['K0']+W)*C-F-v['z']*(q-1))]+list(rows.items())[4:])
    squares=[x*x for x in rows.values()]
    total=squares[0]
    for x in squares[1:]:total=total+x
    live=set()
    def visit(i):
        if i in live:return
        live.add(i);n=d.nodes[i]
        if n[0] in ('add','sub','mul'):visit(n[1]);visit(n[2])
    visit(total.i)
    mapping={old:new for new,old in enumerate(sorted(live))}
    outnodes=[]
    for old in sorted(live):
        n=d.nodes[old]
        outnodes.append([n[0],mapping[n[1]],mapping[n[2]]] if n[0] in ('add','sub','mul') else n)
    counts={op:sum(n[0]==op for n in outnodes) for op in ('add','sub','mul')}
    registers={name:mapping[e.i] for name,e in locals().copy().items() if isinstance(e,Expr) and e.i in mapping}
    degree_certificate={
          20:{'monomial':{'f':8,'F':4,'J3':12},'coefficient':'(3*beta)^12'},
          19:{'monomial':{'eta':4,'h':4,'v_scale':4,'w3':4,'J3':16},'coefficient':'1944^4*beta^16'},
          18:{'monomial':{'h':8,'v_scale':16,'w3':8,'J3':56},'coefficient':'2^32*3^64*beta^56'}
        }[variant]
    if transport and variant==20:degree_certificate={'monomial':{'f':8,'z':4,'J3':16},'coefficient':'(3*beta)^16'}
    result={'schema':'integer-polynomial-dag-v1','name':f'quotient{variant}'+('_transport' if transport else ''),
        'base_variant':variant,'transport_eliminated':transport,
        'domain':'unrestricted integers','variables':variables,'fixed_ports':PORTS,
        'nodes':outnodes,'residuals':{k:mapping[x.i] for k,x in rows.items()},'output':mapping[total.i],
        'named_registers':registers,'variable_count':len(variables),'residual_count':len(rows),
        'operations':sum(counts.values()),'operation_counts':counts,
        'exact_degree':(28 if transport and variant==20 else {20:24,19:32,18:88}[variant]),
        'degree_certificate':degree_certificate,
        'coefficient_binding':'../../coefficients/BINDING.json',
        'proof_status':'Ordinary reduction relative to pinned native calibration; no new Lean or object-language certificate.'}
    return result

def main():
    metrics=[]
    for variant,transport in EXPORTED_VARIANTS:
        packet=make(variant,transport)
        path=ROOT/(packet['name']+'.json');path.write_text(json.dumps(packet,indent=2)+'\n')
        metrics.append({k:packet[k] for k in ['name','variable_count','exact_degree','residual_count','operations','operation_counts']})
    (ROOT/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
    print(json.dumps(metrics,indent=2))
if __name__=='__main__':main()
