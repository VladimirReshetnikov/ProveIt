#!/usr/bin/env python3
"""Explicit twenty-six-integer polynomial for the blank Pell interface.

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

GUARDED = ['J','F','alpha','z','i','eta','zeta']
VARIABLES = [name+'__'+suffix for name in GUARDED for suffix in ('u','v','r')]+['h','T','t','s_integer','w_integer']
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
          domain='unrestricted integers',variables=VARIABLES,
          coefficient_ports=PORTS,gates=gs,outputs=outputs,
          operations=len(gs),multiplications=sum(g['op']=='*' for g in gs),
          additions_subtractions=sum(g['op']!='*' for g in gs))

def build():
    c=Circuit(); A=c.add; S=c.sub; M=c.mul; Q=c.sq
    for name in GUARDED:
        u,v,r=(name+'__'+suffix for suffix in ('u','v','r'))
        Q(name+'__u2',u); Q(name+'__v2',v)
        A(name+'__rp1',r,1); M(name+'__tri',r,name+'__rp1')
        A(name+'__sum2',name+'__u2',name+'__v2')
        A(name+'__sum3',name+'__sum2',name+'__tri')
        A(name,name+'__sum3',1)
    M('s__twice',2,'s_integer'); A('s','s__twice',1)
    Q('w','w_integer')
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
    # Robust positive weights, valid for signed s,T,h,t and either sign of H.
    Q('H2','H'); Q('c4','c2'); Q('T2','T')
    A('T2p1','T2',1); A('a2p5','a2',5)
    M('bound1','T2p1','a2p5'); M('bound2','bound1','H2')
    M('bound3','bound2','i'); M('bound4','bound3','c4')
    A('boundplusb','bound4','b'); M('twobound',2,'boundplusb')
    A('weightM','twobound',1)
    A('Arootp1','Aroot',1); M('H2M','H2','weightM')
    M('Nminus1','H2M','Arootp1'); A('weightN','Nminus1',1)
    M('HM','H','weightM')
    # The two quadratic norms. Formal roots tau^2=Aroot, u^2=Sroot.
    M('Ht','H','t')
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
    M('AnormV2','Aroot','normV2'); S('Norm26','normU2','AnormV2')
    A('guard',1,'Norm26'); M('unitproduct','Nk','Nt')
    M('fullproduct','unitproduct','guard'); S('Polynomial26','fullproduct',1)
    S('index_residual','Nk',1); S('transport_residual','Nt',1)
    Q('index_residual2','index_residual'); Q('transport_residual2','transport_residual')
    Q('Norm26_squared','Norm26'); A('prefix_sos','index_residual2','transport_residual2')
    A('SOS26','prefix_sos','Norm26_squared')
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

def require(ok,message):
    if not ok: raise ValueError(message)

def checks(c):
    import random
    rng=random.Random(21526)
    packet=c.packet(['Polynomial26'])
    for _ in range(48):
        val={x:rng.randrange(-3,4) for x in VARIABLES}
        val.update(beta=15,kappa=19,MC=2,MF=20)
        val.update(J__u=3,J__v=0,J__r=0)
        env=evaluate(packet,val)
        n=norm_direct(env['H'],env['d'],env['e'],
          2*env['Qstrong']*env['v']*env['b'],env['D'],env['Aroot'],env['Sroot'],
          env['P'],env['weightM'],env['weightN'],val['t'])
        require(n==env['Norm26'],'direct norm identity')
        require((1+n)%4 in (1,2),'unit guard')
        require(math.gcd(env['H'],env['d'])==1,'denominator coprimality')
        require(math.gcd(env['H'],env['weightN'])==1,'weight coprimality')
        require(env['Cword']>=0 and env['R']>0,'test outer range')
        require(env['Aroot']>=1 and env['Sroot']>1,'positive radicands')
        require(env['Delta']>env['R'],'Delta bound including X=0')
        require(1<env['b']<env['Qstrong'],'T=0 gap bounds')
        ycap=2*(abs(env['v'])*(math.isqrt(env['D'])+1)+env['b'])
        require(env['weightM']>ycap,'robust auxiliary root bound')
        require(env['weightN']**2*env['Sroot']>
                env['H']**2*(env['weightM']*(math.isqrt(env['Aroot'])+1)+ycap)**2,
                'robust main root dominance')
    # A genuine auxiliary Pell root fixture, independent of the compiler.
    H,d,e,B,D,A,S,P,M,N=3,8,224,108,4,9,25,2,100,10000
    t=1+M*3+N
    require(norm_direct(H,d,e,B,D,A,S,P,M,N,t)==0,'root fixture')
    require(norm_direct(H,d,e,B,D,A,S,P,M,N,t+1)!=0,'near-root fixture')
    return dict(independent_integer_evaluations=48,
       signed_bounds_including_zero_scale='passed',
       denominator_and_unit_guard_checks='passed',
       auxiliary_root_fixture='passed',
       scope='Finite arithmetic checks, not a formal compiler proof.')

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
                for k,bk in enumerate(b):
                    if bk:out[j+k]+=aj*bk
        return trim([v%modulus for v in out])
    env={v:[0,1] for v in VARIABLES}
    for j,name in enumerate(GUARDED):
        env[name+'__u']=[0,j+1]
        env[name+'__v']=[0]
        env[name+'__r']=[0]
    env.update(h=[0,7],T=[0,5],t=[0,11],s_integer=[0,3],w_integer=[0,2])
    env.update({k:[v] for k,v in dict(beta=15,kappa=19,MC=2,MF=20).items()})
    def get(v):return env[v] if isinstance(v,str) else [v%modulus]
    for g in c.packet(['Polynomial26'])['gates']:
        a,b=map(get,g['args'])
        env[g['name']]=mul(a,b) if g['op']=='*' else add(a,b,1 if g['op']=='+' else -1)
    K=add(mul(env['P'],env['P']),env['Sroot'],-1)
    result={name:dict(degree=len(env[name])-1,leading_coefficient=env[name][-1])
       for name in ['d','weightM','weightN','Norm26','Polynomial26']}
    require(result['Norm26']['degree']==3544,'norm degree')
    require(result['Polynomial26']['degree']==3560,'polynomial degree')
    require(len(K)-1==29,'main-root residual degree')
    expected=pow(env['d'][-1],8,modulus)*pow(env['weightN'][-1],16,modulus)*pow(K[-1],8,modulus)%modulus
    require(result['Norm26']['leading_coefficient']==expected,'leading coefficient')
    return dict(modulus=modulus,results=result,
       predicted_norm_leading_coefficient=expected,
       main_root_residual_degree=29,
       scope='Uniform degree proof is separate; specialization checks its nonzero leading form.')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--degree',action='store_true')
    ap.add_argument('--out',type=Path,default=Path(__file__).resolve().parent/'artifacts')
    args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    c=build()
    variants=[('polynomial26',['Polynomial26'],3560),
              ('system26',['Nk','Nt','Norm26'],3544),
              ('residual_system26',['index_residual','transport_residual','Norm26'],3544),
              ('sos26',['SOS26'],7088)]
    receipt=checks(c)
    receipt['variants']=[]
    for name,outputs,degree in variants:
        p=c.packet(outputs)
        if name=='system26':p['comparisons']=[['Nk',1],['Nt',1],['Norm26',0]]
        p.update(exact_total_degree=degree,proof='proofs/INTEGER26_PROOF.md',
          coefficient_interface='Bind all four ports together using COEFFICIENT_BINDING.json and coefficients/T5263_CONSTANTS.json.',
          positive_port_substitution='Pos(u,v,r)=1+u^2+v^2+r(r+1)',
          guarded_ports=GUARDED,other_substitutions={'s':'2*s_integer+1','w':'w_integer^2'})
        require(len(p['variables'])==26,'variable count')
        known=set(p['variables']+p['coefficient_ports'])
        for g in p['gates']:
            require(g['name'] not in known,'duplicate register')
            require(all(type(x) is int or x in known for x in g['args']),'bad operand')
            known.add(g['name'])
        used=set(x for g in p['gates'] for x in g['args'] if isinstance(x,str))
        require(set(p['variables']+p['coefficient_ports'])<=used,'unused port')
        (args.out/(name+'.json')).write_text(json.dumps(p,indent=2)+'\n')
        receipt['variants'].append({k:p[k] for k in ['operations','multiplications','additions_subtractions','exact_total_degree']}|{'name':name})
    if args.degree:receipt['degree_certificate']=degree_check(c)
    (args.out/'verification26.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()


