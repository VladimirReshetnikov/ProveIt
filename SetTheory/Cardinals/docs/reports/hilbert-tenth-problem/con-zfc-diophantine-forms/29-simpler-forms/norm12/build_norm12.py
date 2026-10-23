#!/usr/bin/env python3
"""Emit an explicit twelve-variable Con(ZFC) arithmetic circuit.

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
    add('bound0','v2','D'); mul('bound1',2,'b')
    add('Bnd','bound0','bound1'); mul('HBnd','H','Bnd')
    add('L','HBnd',1); mul('Hr','H','r'); add('S','b0','Hr')

    # Eliminate f and tau first.  Form V=(S+L*u)^2 in Z[u]/(u^2-G).
    # The sign + is immaterial to the final norm; it saves a negation.
    sq('H2','H'); sq('L2','L'); mul('HL2','H2','L2')
    mul('a0','HL2','A'); mul('H2e','H2','e')
    sq('S2','S'); mul('L2G','L2','G'); add('V0','S2','L2G')
    mul('SL','S','L'); mul('V1',2,'SL')
    add('C00','V0','a0'); mul('C01','d','C00'); sub('C0','C01','H2e')
    mul('C1','d','V1'); sq('d2','d'); mul('Kf0','d2','a0')
    mul('Kf',4,'Kf0'); mul('Kc0','Kf','V0'); mul('Kc1','Kf','V1')
    sq('H4','H2'); mul('PU','P','U'); mul('Z0','H4','PU'); mul('Z',4,'Z0')

    def pair_square(prefix,x,y):
        sq(prefix+'xx',x); sq(prefix+'yy',y)
        mul(prefix+'Gyy','G',prefix+'yy')
        add(prefix+'0',prefix+'xx',prefix+'Gyy')
        mul(prefix+'xy',x,y); mul(prefix+'1',2,prefix+'xy')
        return prefix+'0',prefix+'1'

    cs0,cs1=pair_square('Cs','C0','C1')
    # Symmetric identity: (C^2+K-Z)^2-4*C^2*K
    #                  = (C^2-K-Z)^2-4*K*Z.
    # Z is scalar, so this avoids a full multiplication of two pairs.
    sub('W00',cs0,'Kc0'); sub('W0','W00','Z'); sub('W1',cs1,'Kc1')
    ws0,ws1=pair_square('Ws','W0','W1')
    mul('fourZ',4,'Z'); mul('fourKZ0','fourZ','Kc0'); mul('fourKZ1','fourZ','Kc1')
    sub('N0',ws0,'fourKZ0'); sub('N1',ws1,'fourKZ1')
    sq('N00','N0'); sq('N11','N1'); mul('GN11','G','N11'); sub('N','N00','GN11')
    system = dict(name='norm12_system', witnesses=WITNESSES, fixed_numerals=FIXED,
                  domain='strictly positive integers', source=deepcopy(s),
                  comparisons=[['Nk',1],['Nt',1],['N',0]],
                  residual_exact_degrees=[7,2,1344],
                  coefficient_binding='Use one complete certified tuple: beta=B-1, K0=D_C+B*D_R, MC, shifted MF.')

    add('guard',1,'N'); mul('KN','Nk','Nt'); mul('prod','KN','guard'); sub('polynomial','prod',1)
    product = dict(system, name='norm12_product', source=deepcopy(s), output='polynomial', exact_degree=1353)
    product.pop('comparisons'); product.pop('residual_exact_degrees')
    s[:] = deepcopy(system['source'])
    sub('rk','Nk',1); sq('rksq','rk'); sub('rt','Nt',1); sq('rtsq','rt')
    sq('Nsq','N'); add('sos0','rksq','rtsq'); add('sos','sos0','Nsq')
    sos = dict(system, name='norm12_sos', source=deepcopy(s), output='sos', exact_degree=2688)
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
    out=[p['output']] if 'output' in p else [a for a,b in p['comparisons']]
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


def integer26_lift(p):
    """Use the separately proved seven-positive-coordinate domain extension.

    Pos(x,y,t)=1+x^2+y^2+t(t+1) is positive and represents every
    positive integer (the classical two-squares plus pronic theorem).
    The remaining special coordinates are i=2*ii+1 and w=ww^2.
    """
    q=deepcopy(p);prefix=[];witnesses=[]
    for n in ['J','F','alpha','z','s','eta','zeta']:
        x,y,t=[n+'_'+v for v in ['x','y','t']];witnesses += [x,y,t]
        prefix += [[n+'_x2','*',x,x],[n+'_y2','*',y,y],
                   [n+'_tp1','+',t,1],[n+'_pronic','*',t,n+'_tp1'],
                   [n+'_sum0','+',n+'_x2',n+'_y2'],
                   [n+'_sum1','+',n+'_sum0',n+'_pronic'],[n,'+',n+'_sum1',1]]
    witnesses += ['ii','ww','h','T','r']
    prefix += [['twice_ii','*',2,'ii'],['i','+','twice_ii',1],['w','*','ww','ww']]
    q.update(name=p['name']+'_integer26',source=prefix+q['source'],
             witnesses=witnesses,domain='unrestricted integers')
    q.pop('ledger',None)
    if 'output' in q:q['exact_degree']=2657 if q['output']=='polynomial' else 5280
    else:q['residual_exact_degrees']=[13,4,2640]
    return q


def pair_product(x,y,g):return (x[0]*y[0]+g*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def pair_sum(x,y):return (x[0]+y[0],x[1]+y[1])
def pair_scale(x,a):return (a*x[0],a*x[1])


def independent_norm(a):
    """Direct multiplication in Q[u,tau,f]/(u^2-G,tau^2-A,f^2-D).

    Multiply all eight conjugates of d(S-L*u-H*L*tau)^2-H^2*e+H^2*B*f.
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
        root=[a['S'],-su*a['L'],-st*a['H']*a['L'],0,0,0,0,0]
        w=[a['d']*x for x in product(root,root)]
        w[0]-=a['H']**2*a['e'];w[4]+=sf*a['H']**2*B
        acc=product(acc,w)
    if any(acc[1:]):raise ValueError('Conjugate product failed to descend')
    return acc[0]


def diagnostics(ps):
    rng=random.Random(120022); fixtures=24
    for _ in range(fixtures):
        vals={n:rng.randrange(-2,4) for n in WITNESSES+FIXED}
        a=evaluate(ps[0],vals)
        if a['N']!=independent_norm(a):raise ValueError('Norm identity failure')
        if evaluate(ps[1],vals)['polynomial'] != a['Nk']*a['Nt']*(1+a['N'])-1:raise ValueError('Product failure')
        if evaluate(ps[2],vals)['sos'] != (a['Nk']-1)**2+(a['Nt']-1)**2+a['N']**2:raise ValueError('SOS failure')
        if a['N1']%8 or (a['N']-a['N0']**2)%64:raise ValueError('Modular guard failure')
    # Homogeneous leading coefficients certify actual degrees in these fixed slices.
    # No full dense expansion is required for this diagnostic.
    witnesses=[]
    for prime,seed in [(1000000007,1201),(1000000009,1202)]:
      rng=random.Random(seed)
      lead={n:(1,rng.randrange(1,prime)) for n in WITNESSES}
      lead.update({n:(0,c) for n,c in zip(FIXED,[31,127,10,45])})
      degrees=ledger(ps[0])
      for n,op,l,r in ps[0]['source']:
        dl,cl=(0,l%prime) if isinstance(l,int) else lead[l]
        dr,cr=(0,r%prime) if isinstance(r,int) else lead[r]
        if op=='*':lead[n]=(dl+dr,cl*cr%prime)
        else:
            deg=max(dl,dr);coef=((cl if dl==deg else 0)+(cr if dr==deg else 0)*(1 if op=='+' else -1))%prime
            lead[n]=(deg,coef)
      for n,deg in [('Nk',7),('Nt',2),('N',1344)]:
        if lead[n][0]!=deg or not lead[n][1]:raise ValueError(('Leading form vanished',n,lead[n]))
      witnesses.append({'prime':prime,'seed':seed,'leading_values':{n:lead[n] for n in ['Nk','Nt','N']}})
    return {'signed_exact_conjugate_product_fixtures':fixtures,
            'modular_guard_fixtures':fixtures,'leading_form_diagnostics':witnesses,
            'scope':'Exact circuit identities and size only; no accepting K215 run or semantic compiler verification.'}


def main():
    ps=construct()
    for p in ps:ledger(p)
    checks=diagnostics(ps)
    integer_ps=[integer26_lift(p) for p in ps]
    for p in integer_ps:ledger(p)
    rng=random.Random(2612)
    for _ in range(24):
        vals={n:rng.randrange(-2,4) for n in integer_ps[0]['witnesses']+FIXED}
        back={n:vals[n+'_x']**2+vals[n+'_y']**2+vals[n+'_t']*(vals[n+'_t']+1)+1
              for n in ['J','F','alpha','z','s','eta','zeta']}
        back.update(i=2*vals['ii']+1,w=vals['ww']**2,h=vals['h'],T=vals['T'],r=vals['r'])
        back.update({n:vals[n] for n in FIXED})
        for p,ip in zip(ps,integer_ps):
            av=evaluate(p,back);bv=evaluate(ip,vals)
            out=[p['output']] if 'output' in p else ['Nk','Nt','N']
            if any(av[n]!=bv[n] for n in out):raise ValueError('Integer substitution failure')
    checks['integer26_substitution_fixtures']=24
    all_packets=ps+integer_ps
    for p in all_packets:(HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
    receipt={'packets':[{k:p[k] for k in ['name','ledger']} for p in all_packets],'checks':checks}
    (HERE/'norm12_checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()

