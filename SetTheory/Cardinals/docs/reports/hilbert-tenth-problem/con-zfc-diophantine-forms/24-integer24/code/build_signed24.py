#!/usr/bin/env python3
"""Emit a degree-1936 circuit over 24 unrestricted integers.

Combines the normalized-odd-part evaluator with the separately proved signed
weights and domain lift. Semantic proof and coefficient binding accompany
the enclosing report. All imports use the Python standard library.

This is an algebra and size audit, not a proof of the inherited compiler.
All +,-,* gates, including multiplication by literal constants, are charged.
No upstream imports or third-party Python packages are required.
"""
from collections import Counter
from copy import deepcopy
from pathlib import Path
import json
import random

HERE = Path(__file__).resolve().parent
CIRCUITS = HERE.parent/'circuits'
EVIDENCE = HERE.parent/'evidence'
WITNESSES = ['J','F','alpha','z','h','i','T','s','w','eta','zeta','r']
FIXED = ['beta','K0','MC','MF']


def construct():
    s = []
    def gate(n, op, a, b):
        s.append([n,op,a,b]); return n
    def add(n,a,b): return gate(n,'+',a,b)
    def sub(n,a,b): return gate(n,'-',a,b)
    def mul(n,a,b): return gate(n,'*',a,b)
    def sq(n,a): return mul(n,a,a)

    mul('qm1','beta','J'); add('q','qm1',1)
    sq('q2','q'); mul('q3','q2','q')
    mul('X','w','q'); mul('Y','s','q3'); mul('E','X','Y')
    add('k','eta','zeta'); mul('kY','k','Y')
    mul('ell','E','kY'); add('ellk','ell','k')
    mul('ellprod','ell','ellk'); add('A','ellprod',1)
    add('c','kY','eta'); add('a','E','Y'); mul('ac','a','c')
    add('b0','X','ac'); mul('foura',4,'a'); add('H','foura',3)
    sq('a2','a'); add('Delta','a2','H'); sq('c2','c')
    mul('Deltac2','Delta','c2'); add('G','Deltac2',1)
    sub('qmF','q','F'); sub('Cw','qmF','alpha')
    mul('hE','h','E'); sub('index0','k','hE')
    mul('pack0','qm1','qmF'); add('pack1','pack0','alpha')
    sub('q2m1','q2',1); mul('pack2','pack1','q2m1')
    mul('qMF','q','MF'); add('mask0','MC','qMF')
    mul('mask1','mask0','J'); add('R','pack2','mask1')
    sub('Nk','index0','R'); add('Kplusw','K0','w')
    mul('trans0','Kplusw','Cw'); add('trans1','trans0','qmF')
    mul('trans2','z','qm1'); sub('Nt','trans1','trans2')
    mul('Qr','i','Deltac2'); sq('Q','Qr')
    mul('I','i','c2'); mul('Dm1','I','Qr'); add('D','Dm1',1)
    mul('v','c','T'); sq('v2','v'); mul('RD','R','D')
    add('b','c','RD'); mul('Dv2','D','v2'); sq('b2','b')
    mul('P','Q','Dv2'); mul('U','Q','b2'); add('eplus1','P','U')
    sub('e','eplus1',1); sub('d','Q',1)
    mul('ic','i','c'); sq('T2','T'); mul('T2c','T2','c')
    mul('Ra','R','a'); mul('twiceRa',2,'Ra'); add('weight0','T2c','twiceRa')
    mul('icI','ic','I'); mul('weight1','icI','weight0'); mul('M0',8,'weight1'); add('M','M0',1)
    mul('m','H','M'); mul('twom',8,'m'); add('L','twom',1)
    mul('Hr','H','r'); mul('Lb0','L','b0'); add('S','Lb0','Hr')

    # Eliminate f and tau first.  Form V=(S+L*u)^2 with S=H*r+L*b0 and m=H*M in Z[u]/(u^2-G).
    # The sign + is immaterial to the final norm; it saves a negation.
    sq('H2','H'); sq('L2','L'); sq('m2','m')
    mul('a0','m2','A'); mul('H2e','H2','e')
    sq('S2','S'); mul('L2G','L2','G'); add('V0','S2','L2G')
    mul('theta2pre','S2','L2G'); mul('theta2',4,'theta2pre')
    add('C00','V0','a0'); mul('C01','d','C00'); sub('C0','C01','H2e')
    sq('d2','d'); mul('Kf0','d2','a0')
    mul('Kf',4,'Kf0'); mul('Kc0','Kf','V0')
    sq('H4','H2'); mul('PU','P','U'); mul('Z0','H4','PU'); mul('Z',4,'Z0')

    def pair_square(prefix,x,y):
        sq(prefix+'xx',x); sq(prefix+'yy',y)
        mul(prefix+'Gyy','theta2',prefix+'yy')
        add(prefix+'0',prefix+'xx',prefix+'Gyy')
        mul(prefix+'xy',x,y); mul(prefix+'1',2,prefix+'xy')
        return prefix+'0',prefix+'1'

    sq('Csxx','C0'); mul('CsGyy','theta2','d2'); add('Cs0','Csxx','CsGyy')
    mul('Csxy','C0','d'); mul('Cs1',2,'Csxy'); cs0,cs1='Cs0','Cs1'
    # Symmetric identity: (C^2+K-Z)^2-4*C^2*K
    #                  = (C^2-K-Z)^2-4*K*Z.
    # Z is scalar, so this avoids a full multiplication of two pairs.
    sub('W00',cs0,'Kc0'); sub('W0','W00','Z'); sub('W1',cs1,'Kf')
    ws0,ws1=pair_square('Ws','W0','W1')
    mul('fourZ',4,'Z'); mul('fourKZ0','fourZ','Kc0'); mul('fourKZ1','fourZ','Kf')
    sub('N0',ws0,'fourKZ0'); sub('N1',ws1,'fourKZ1')
    sq('N00','N0'); sq('N11','N1'); mul('GN11','theta2','N11')
    system = dict(name='signed_separating_saturated24_system', witnesses=WITNESSES, fixed_numerals=FIXED,
                  domain='strictly positive integers', source=deepcopy(s),
                  comparisons=[['Nk',1],['Nt',1],['N00','GN11']],
                  residual_exact_degrees=[7,2,1072],
                  coefficient_binding='Use one complete certified tuple: beta=B-1, K0=D_C+B*D_R, MC, shifted MF.')

    sub('N','N00','GN11'); add('guard',1,'N'); mul('KN','Nk','Nt'); mul('prod','KN','guard'); sub('polynomial','prod',1)
    product = dict(system, name='signed_separating_saturated24_product', source=deepcopy(s), output='polynomial', exact_degree=1081)
    product.pop('comparisons'); product.pop('residual_exact_degrees')
    s[:] = deepcopy(system['source']); sub('N','N00','GN11')
    sub('rk','Nk',1); sq('rksq','rk'); sub('rt','Nt',1); sq('rtsq','rt')
    sq('Nsq','N'); add('sos0','rksq','rtsq'); add('sos','sos0','Nsq')
    sos = dict(system, name='signed_separating_saturated24_sos', source=deepcopy(s), output='sos', exact_degree=2144)
    sos.pop('comparisons'); sos.pop('residual_exact_degrees')
    return [system, product, sos]


def ledger(p):
    names=set(p['witnesses']+p['fixed_numerals'])
    degree={n:1 for n in p['witnesses']};degree.update({n:0 for n in p['fixed_numerals']})
    for n,op,a,b in p['source']:
        if n in names or op not in ('+','-','*'): raise ValueError((n,op))
        if any(not isinstance(x,int) and x not in names for x in (a,b)):raise ValueError((n,a,b))
        names.add(n)
        da=0 if isinstance(a,int) else degree[a];db=0 if isinstance(b,int) else degree[b]
        degree[n]=da+db if op=='*' else max(da,db)
    out=[p['output']] if 'output' in p else [x for row in p['comparisons'] for x in row if isinstance(x,str)]
    live=set(out)
    for n,_,a,b in reversed(p['source']):
        if n in live:live.update(x for x in (a,b) if isinstance(x,str))
    if any(n not in live for n,_,_,_ in p['source']):raise ValueError('Dead gates')
    if not set(p['witnesses']+p['fixed_numerals'])<=live:raise ValueError('Unused ports')
    ct=Counter(row[1] for row in p['source'])
    p['ledger']={'operations':len(p['source']),'multiplications':ct['*'],
                 'additions_subtractions':ct['+']+ct['-'],'all_gates_live':True,'all_ports_live':True,
                 'syntactic_degree_upper_bounds':{n:degree[n] for n in out}}
    return degree


def evaluate(p,values):
    a=dict(values)
    for n,op,l,r in p['source']:
        l=l if isinstance(l,int) else a[l];r=r if isinstance(r,int) else a[r]
        a[n]=l+r if op=='+' else l-r if op=='-' else l*r
    return a


def pair_product(x,y,g):return (x[0]*y[0]+g*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def pair_sum(x,y):return (x[0]+y[0],x[1]+y[1])
def pair_scale(x,a):return (a*x[0],a*x[1])


def independent_norm(a):
    """Direct multiplication in Q[u,tau,f]/(u^2-G,tau^2-A,f^2-D).

    Multiply all eight conjugates of d(S-L*u-m*tau)^2-H^2*e+H^2*B*f.
    This independent eight-component implementation shares no norm-gate derivation.
    """
    G,A,D=a['G'],a['A'],a['D']
    def product(x,y):
        z=[0]*8
        for i,v in enumerate(x):
            for j,w in enumerate(y):
                factor=1
                if i&j&1:factor*=G
                if i&j&2:factor*=A
                if i&j&4:factor*=D
                z[i^j]+=factor*v*w
        return z
    B=2*a['Q']*a['v']*a['b'];acc=[1]+[0]*7
    for su in (-1,1):
      for st in (-1,1):
       for sf in (-1,1):
        root=[a['S'],-su*a['L'],-st*a['m'],0,0,0,0,0]
        w=[a['d']*x for x in product(root,root)]
        w[0]-=a['H']**2*a['e'];w[4]+=sf*a['H']**2*B
        acc=product(acc,w)
    if any(acc[1:]):raise ValueError('Conjugate product failed to descend')
    return acc[0]


def lift24(packet):
    q=deepcopy(packet);prefix=[];names=[]
    for n in ['J','F','alpha','z','eta','zeta']:
        x,y,t=[n+'_'+v for v in ['x','y','t']];names += [x,y,t]
        prefix += [[n+'_x2','*',x,x],[n+'_y2','*',y,y],
                   [n+'_tp1','+',t,1],[n+'_pronic','*',t,n+'_tp1'],
                   [n+'_sum0','+',n+'_x2',n+'_y2'],
                   [n+'_sum1','+',n+'_sum0',n+'_pronic'],[n,'+',n+'_sum1',1]]
    names += ['ii','ss','ww','h','T','r']
    prefix += [['twice_ii','*',2,'ii'],['i','+','twice_ii',1],
               ['twice_ss','*',2,'ss'],['s','+','twice_ss',1],['w','*','ww','ww']]
    # F=F_sum1+1 and z=z_sum1+1. Cancel their two constant
    # shifts against q=qm1+1 and the old transport's qmF term.
    prefix=[row for row in prefix if row[0] not in ['F','z']]
    body=[]
    for n,op,a,b in q['source']:
        if n=='qmF':body.append([n,'-','qm1','F_sum1'])
        elif n=='trans1':body.append([n,'-','trans0','F_sum1'])
        elif n=='trans2':body.append([n,'*','z_sum1','qm1'])
        else:body.append([n,op,a,b])
    q.update(source=prefix+body,witnesses=names,domain='unrestricted integers')
    q.pop('ledger',None)
    if 'output'in q:q['exact_degree']=1936 if q['output']=='polynomial'else 3840
    else:q['residual_exact_degrees']=[12,4,1920]
    return q

def main():
    ps=construct(); qs=[lift24(p) for p in ps]
    checks=[]
    for p in qs:
        degrees=ledger(p)
        if 'output'in p:
            if degrees[p['output']]!=p['exact_degree']:raise ValueError('degree bound')
        else:
            actual=[max(degrees.get(x,0) if isinstance(x,str)else 0 for x in row)for row in p['comparisons']]
            if actual!=p['residual_exact_degrees']:raise ValueError(('degree bounds',actual,p['residual_exact_degrees']))
    rng=random.Random(241936)
    for _ in range(40):
        vals={n:rng.randrange(-2,3)for n in qs[1]['witnesses']+FIXED}
        a=evaluate(qs[1],vals)
        if a['N']!=independent_norm(a):raise ValueError('Norm identity failure')
        if a['theta2']%4 or (a['N']-a['N0']**2)%4:raise ValueError('Modular guard failure')
        back={n:a[n]for n in WITNESSES+FIXED if n not in ['F','z']};back.update(F=a['F_sum1']+1,z=a['z_sum1']+1)
        for p,q in zip(ps,qs):
            av=evaluate(p,back);bv=evaluate(q,vals)
            outs=[p['output']]if 'output'in p else ['Nk','Nt','N00','GN11']
            if any(av[n]!=bv[n]for n in outs):raise ValueError('Lift identity')
    receipt={'packets':[{k:p[k]for k in ['name','ledger','witnesses']}for p in qs],
             'checks':{'independent_eight_conjugate_product_cases':40,'domain_substitution_cases':120,
                       'all_gates_and_inputs_live':True,
                       'scope':'Arithmetic checks only. Semantic signed-domain proof must be supplied independently.'}}
    for p in qs:(CIRCUITS/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
    (EVIDENCE/'signed24_checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
