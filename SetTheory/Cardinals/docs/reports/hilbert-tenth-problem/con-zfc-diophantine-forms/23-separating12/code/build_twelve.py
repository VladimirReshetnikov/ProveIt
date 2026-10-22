#!/usr/bin/env python3
"""Explicit twelve-positive-variable polynomial for the blank Pell interface.

Four fixed coefficient ports must be bound to ONE certified blank compiler.
Every displayed register is an abbreviation, never another unknown.
Only the standard library is required to emit, evaluate, and check the DAG,
including the optional --degree diagnostic.
"""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path

VARIABLES = ['J','F','alpha','z','h','i','T','s','w','eta','zeta','t']
PORTS = ['beta','kappa','MC','MF']

class Circuit:
    def __init__(self):
        self.gates=[]
    def op(self, name, op, a, b):
        self.gates.append(dict(name=name,op=op,args=[a,b]))
        return name
    def add(self,n,a,b): return self.op(n,'+',a,b)
    def sub(self,n,a,b): return self.op(n,'-',a,b)
    def mul(self,n,a,b): return self.op(n,'*',a,b)
    def sq(self,n,a): return self.mul(n,a,a)
    def live(self, outputs):
        gates={g['name']:g for g in self.gates}; needed=set()
        def visit(x):
            if isinstance(x,str) and x in gates and x not in needed:
                needed.add(x)
                for y in gates[x]['args']:visit(y)
        for x in outputs:visit(x)
        return [g for g in self.gates if g['name'] in needed]
    def packet(self, outputs):
        gs=self.live(outputs)
        return dict(format='named-binary-arithmetic-circuit-v1',
          domain='strictly positive integers',variables=VARIABLES,
          coefficient_ports=PORTS,gates=gs,outputs=outputs,
          operations=len(gs),multiplications=sum(g['op']=='*' for g in gs),
          additions_subtractions=sum(g['op']!='*' for g in gs))

def build():
    c=Circuit(); A=c.add; S=c.sub; M=c.mul; Q=c.sq
    M('q0','beta','J'); A('q','q0',1); Q('q2','q')
    M('q3','q2','q'); S('qF','q','F'); S('Cword','qF','alpha')
    M('X','w','q'); M('Y','s','q3'); M('E','X','Y')
    A('k','eta','zeta'); M('kY','k','Y'); A('c','kY','eta')
    Q('c2','c'); M('c3','c2','c'); A('a','E','Y')
    M('foura',4,'a'); A('H','foura',3); Q('a2','a')
    A('Delta','a2','H'); M('ac','a','c'); A('P','X','ac')
    M('Delta_c2','Delta','c2'); A('Sroot','Delta_c2',1)
    M('L','E','kY'); A('Lk','L','k'); M('Lprod','L','Lk')
    A('Aroot','Lprod',1)
    M('rprefix','q0','qF'); A('rprefix_alpha','rprefix','alpha')
    S('q2m1','q2',1); M('rlow','rprefix_alpha','q2m1')
    M('qMF','q','MF'); A('mask','MC','qMF'); M('maskJ','mask','J')
    A('R','rlow','maskJ')
    M('hE','h','E'); S('k_hE','k','hE'); S('Nk','k_hE','R')
    A('kappaw','kappa','w'); M('transport','kappaw','Cword')
    A('transport_qF','transport','qF'); M('zq0','z','q0')
    S('Nt','transport_qF','zq0')
    # H-divisible normalized strong multiplier. G=H*i*c^2.
    M('Hi','H','i'); M('G','Hi','c2'); Q('G2','G')
    M('D0','Delta','G2'); A('D','D0',1); M('Qstrong','Delta','D0')
    S('d','Qstrong',1); M('v','c','T'); Q('v2','v')
    M('RD','R','D'); A('b','c','RD'); Q('b2','b')
    M('Dv2','D','v2'); A('sum_Dv2_b2','Dv2','b2')
    M('Qsum','Qstrong','sum_Dv2_b2'); S('e','Qsum',1)
    # Explicit separating weights.
    Q('Hi2','Hi'); M('W0','Hi2','c3'); M('RW0','R','W0')
    M('TG','T','G'); M('eightTG',8,'TG'); M('ERW0','E','RW0')
    M('sixteenERW0',16,'ERW0'); A('Mpartial',1,'eightTG')
    A('weightM','Mpartial','sixteenERW0')
    M('HM','H','weightM'); M('twoHM',2,'HM'); A('weightN','twoHM',1)
    # The two quadratic norms. Formal roots tau^2=Aroot, u^2=Sroot.
    Q('H2','H'); M('Ht','H','t')
    M('NP','weightN','P'); A('W','Ht','NP'); Q('W2','W')
    Q('HM2','HM'); M('HM2A','HM2','Aroot'); Q('N2','weightN')
    M('N2S','N2','Sroot'); A('diagonal1','W2','HM2A')
    A('diagonal','diagonal1','N2S'); M('ddiagonal','d','diagonal')
    M('H2e','H2','e'); S('a0','ddiagonal','H2e')
    M('twod',2,'d'); M('twodW','twod','W')
    M('p','twodW','HM'); M('qcoef','twodW','weightN')
    M('twodHM','twod','HM'); M('r','twodHM','weightN')
    # H^4 B^2 D=4(H^2 Q)^2 (D v^2)b^2, B=2Qvb.
    M('H2Q','H2','Qstrong'); Q('H2Q2','H2Q')
    M('constant1','H2Q2','Dv2'); M('constant2','constant1','b2')
    M('constant',4,'constant2')
    Q('a02','a0'); Q('p2','p'); M('Ap2','Aroot','p2')
    Q('qcoef2','qcoef'); Q('r2','r'); M('Ar2','Aroot','r2')
    A('q2Ar2','qcoef2','Ar2'); M('Sblock','Sroot','q2Ar2')
    A('f0partial','a02','Ap2'); A('f0pre','f0partial','Sblock')
    S('f0','f0pre','constant')
    M('a0p','a0','p'); M('qr','qcoef','r'); M('Sqr','Sroot','qr')
    A('p1half','a0p','Sqr'); M('p1',2,'p1half')
    M('a0q','a0','qcoef'); M('pr','p','r'); M('Apr','Aroot','pr')
    A('p2half','a0q','Apr'); M('p2coef',2,'p2half')
    M('a0r','a0','r'); M('pq','p','qcoef')
    A('f3half','a0r','pq'); M('f3',2,'f3half')
    Q('f02','f0'); Q('p12','p1'); M('Ap12','Aroot','p12')
    Q('p22','p2coef'); Q('f32','f3'); M('Af32','Aroot','f32')
    A('normblock','p22','Af32'); M('Snormblock','Sroot','normblock')
    A('normdiag','f02','Ap12'); S('normU','normdiag','Snormblock')
    M('f0p1','f0','p1'); M('p2f3','p2coef','f3')
    M('Sp2f3','Sroot','p2f3'); S('normVhalf','f0p1','Sp2f3')
    M('normV',2,'normVhalf'); Q('normU2','normU'); Q('normV2','normV')
    M('AnormV2','Aroot','normV2'); S('Norm12','normU2','AnormV2')
    A('guard',1,'Norm12'); M('unitproduct','Nk','Nt')
    M('fullproduct','unitproduct','guard'); S('Polynomial12','fullproduct',1)
    S('index_residual','Nk',1); S('transport_residual','Nt',1)
    Q('index_residual2','index_residual'); Q('transport_residual2','transport_residual')
    Q('Norm12_squared','Norm12'); A('prefix_sos','index_residual2','transport_residual2')
    A('SOS12','prefix_sos','Norm12_squared')
    return c

def evaluate(packet, values):
    env=dict(values)
    for g in packet['gates']:
        a,b=(env[x] if isinstance(x,str) else x for x in g['args'])
        env[g['name']]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[g['op']]()
    return env

def norm_direct(H,d,e,B,D,A,S,P,M,N,t):
    """Independent direct coefficient implementation of the norm."""
    W=H*t+N*P
    aa=d*(W*W+(H*M)**2*A+N*N*S)-H*H*e
    bb=-2*d*W*H*M; cc=-2*d*W*N; dd=2*d*H*M*N
    f0=aa*aa+A*bb*bb+S*cc*cc+A*S*dd*dd-H**4*B*B*D
    f1=2*(aa*bb+S*cc*dd)
    f2=2*(aa*cc+A*bb*dd)
    f3=2*(aa*dd+bb*cc)
    U=f0*f0+A*f1*f1-S*(f2*f2+A*f3*f3)
    V=2*(f0*f1-S*f2*f3)
    return U*U-A*V*V

def checks(c):
    import random
    rng=random.Random(21512)
    p=c.packet(['Polynomial12'])
    for _ in range(24):
        val={x:rng.randrange(1,5) for x in VARIABLES+PORTS}
        env=evaluate(p,val)
        n=norm_direct(env['H'],env['d'],env['e'],
          2*env['Qstrong']*env['v']*env['b'],env['D'],env['Aroot'],env['Sroot'],
          env['P'],env['weightM'],env['weightN'],val['t'])
        assert n==env['Norm12']
        assert (1+n)%4 in (1,2)
        assert math.gcd(env['H'],env['d'])==1
        assert math.gcd(env['H'],env['weightN'])==1
    H,d,e,B,D,A,S,P,M,N=3,8,224,108,4,9,25,2,100,10000
    t=1+M*3+N*1
    assert norm_direct(H,d,e,B,D,A,S,P,M,N,t)==0
    assert norm_direct(H,d,e,B,D,A,S,P,M,N,t+1)!=0
    return dict(independent_integer_evaluations=24,
      toy_exact_root=dict(H=H,d=d,e=e,B=B,D=D,A=A,S=S,P=P,M=M,N=N,t=t),
      gcd_checks='passed',unit_guard_mod4='passed',
      note='These finite checks supplement the general proof; no K215 witness is claimed.')

def degree_check(c):
    modulus=1000000007
    def trim(p):
        while len(p)>1 and not p[-1]:p.pop()
        return p
    def add(a,b,sign=1):
        out=a.copy()+[0]*max(0,len(b)-len(a))
        for j,v in enumerate(b):out[j]=(out[j]+sign*v)%modulus
        return trim(out)
    def mul(a,b):
        out=[0]*(len(a)+len(b)-1)
        for j,aj in enumerate(a):
            if aj:
                for k,bk in enumerate(b):out[j+k]+=aj*bk
        return trim([v%modulus for v in out])
    env={v:[0,j+1] for j,v in enumerate(VARIABLES)}
    env.update({k:[v] for k,v in dict(beta=16,kappa=19,MC=23,MF=29).items()})
    def get(v):return env[v] if isinstance(v,str) else [v%modulus]
    for g in c.packet(['Polynomial12'])['gates']:
        a,b=map(get,g['args'])
        env[g['name']]={'+':lambda:add(a,b),'-':lambda:add(a,b,-1),'*':lambda:mul(a,b)}[g['op']]()
    result={name:dict(degree=len(env[name])-1,leading_coefficient=env[name][-1])
       for name in ['weightM','weightN','Norm12','Polynomial12']}
    assert result['Norm12']['degree']==1360,result
    assert result['Polynomial12']['degree']==1369,result
    C=15**4*17**4*(47*49*79*81)**2
    expected=C*pow(env['d'][-1],8,modulus)*pow(env['H'][-1],16,modulus)*pow(env['b'][-1],16,modulus)%modulus
    assert result['Norm12']['leading_coefficient']==expected
    return dict(modulus=modulus,substitution='variable j -> (j+1)x',results=result,
       predicted_norm_leading_coefficient=expected,
       qualification='This specialization is a lower-degree certificate; the general leading-form proof supplies the uniform upper bound and nonvanishing.')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--degree',action='store_true')
    ap.add_argument('--out',type=Path,default=Path(__file__).resolve().parent/'artifacts')
    args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    c=build();p=c.packet(['Polynomial12']);s=c.packet(['Nk','Nt','Norm12'])
    r=c.packet(['index_residual','transport_residual','Norm12']);ss=c.packet(['SOS12'])
    p.update(total_degree=1369,degree_in_t=16)
    s.update(maximum_total_degree=1360,
       comparisons=[dict(left='Nk',right=1),dict(left='Nt',right=1),dict(left='Norm12',right=0)],
       counting_convention='The three final comparisons are free; every binary arithmetic gate is charged.')
    r.update(maximum_total_degree=1360,equations='Every output equals zero.')
    ss.update(total_degree=2720,degree_in_t=32)
    for name,data in [('polynomial12.json',p),('system12.json',s),
                      ('residual_system12.json',r),('sos12.json',ss)]:
        (args.out/name).write_text(json.dumps(data,indent=2)+'\n')
    receipt=checks(c)
    receipt['polynomial_metrics']={k:p[k] for k in ['operations','multiplications','additions_subtractions','total_degree','degree_in_t']}
    receipt['system_metrics']={k:s[k] for k in ['operations','multiplications','additions_subtractions','maximum_total_degree']}
    receipt['residual_system_metrics']={k:r[k] for k in ['operations','multiplications','additions_subtractions','maximum_total_degree']}
    receipt['sos_metrics']={k:ss[k] for k in ['operations','multiplications','additions_subtractions','total_degree','degree_in_t']}
    if args.degree:receipt['degree_diagnostic']=degree_check(c)
    (args.out/'verification12.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
