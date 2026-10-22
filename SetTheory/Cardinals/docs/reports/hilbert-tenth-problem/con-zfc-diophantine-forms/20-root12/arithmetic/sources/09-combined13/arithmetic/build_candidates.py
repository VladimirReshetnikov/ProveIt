#!/usr/bin/env python3
"""Explicit circuit experiments for the fixed blank K215 slice.

All arithmetic counts charge binary +, -, * including numeral products.
Checks below audit algebra; they are not the semantic compiler proof.
"""
from pathlib import Path
import json, random
from collections import Counter
from fractions import Fraction

HERE=Path(__file__).resolve().parent
COEFFICIENT_BINDING={
    'manifest':'../COEFFICIENT_BINDINGS.json',
    'default_recipe_from_package_root':'compiler/tshape_constants.json',
    'arithmetic_interface_origin':'06-blank67',
    'mask_convention':'MF is the shifted mask port',
}

def read(name): return json.loads((HERE/name).read_text())
def write(name,obj): (HERE/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')

def evaluate(source,values):
    vals=dict(values)
    for n,op,a,b in source:
        a=a if type(a) is int else vals[a]
        b=b if type(b) is int else vals[b]
        vals[n]=a+b if op=='+' else a-b if op=='-' else a*b
    return vals

def ledger(p):
    source=p['source']; free=p['witnesses']+p['fixed_numerals']; known=set(free)
    for n,op,a,b in source:
        assert n not in known and op in ('+','-','*')
        assert all(type(x) is int or x in known for x in (a,b))
        known.add(n)
    outputs=[p['output']] if 'output' in p else [x for row in p['comparisons'] for x in row if type(x) is str]
    need=set(outputs)
    for n,op,a,b in reversed(source):
        if n in need: need.update(x for x in (a,b) if type(x) is str)
    assert all(n in need for n,_,_,_ in source)
    assert set(free)<=need
    count=Counter(row[1] for row in source)
    p['ledger']={'operations':len(source),'multiplications':count['*'],
                 'additions_subtractions':count['+']+count['-'],
                 'all_gates_live':True,'all_ports_live':True}
    return p

def construct13():
    base=read('p13_initial.json')
    s=base['source']; cut=next(i for i,row in enumerate(s) if row[0]=='PU')
    s=s[:cut]+[
      ['PU','*','P','UQ'], ['LN','*','L','N'],
      ['norm_gap','-','PU','LN'], ['four_gap','*',4,'norm_gap'],
      ['UU','+','Cr2','four_gap'], ['UU2','*','UU','UU'],
      ['C2PU','*','Cr2','PU'], ['sixteenC2PU','*',16,'C2PU']]
    p={k:v for k,v in base.items() if k not in ('ledger','source','comparisons')}
    p.update(name='system13_78',source=s,
       comparisons=[['norm_main',1],['norm_index',1],['norm_transport',1],['UU2','sixteenC2PU']],
       residual_exact_degrees=[18,7,2,544], domain='strictly positive integers')
    ledger(p)
    # Four-square finalizer; every comparison residual is explicitly charged.
    sos=json.loads(json.dumps(p)); ss=list(s)
    for j,(a,b) in enumerate(p['comparisons']):
        ss += [[f'residual{j}','-',a,b],[f'square{j}','*',f'residual{j}',f'residual{j}']]
    ss += [['sum1','+','square0','square1'],['sum2','+','sum1','square2'],['SOS','+','sum2','square3']]
    sos.pop('comparisons'); sos.update(name='sos13_89',source=ss,output='SOS',exact_degree=1088)
    ledger(sos)
    prod=json.loads(json.dumps(p)); ps=list(s)+[
      ['norm13','-','UU2','sixteenC2PU'],['unit13','+','norm13',1],
      ['Ptwo','*','norm_main','norm_index'],['Pthree','*','Ptwo','norm_transport'],
      ['all','*','Pthree','unit13'],['polynomial','-','all',1]]
    prod.pop('comparisons'); prod.update(name='polynomial13_84',source=ps,output='polynomial',exact_degree=571)
    ledger(prod)
    return p,sos,prod

def lower_weight13(base):
    """A one-operation, lower-degree weight, with its own positivity proof."""
    p=json.loads(json.dumps(base));s=[]
    for n,op,a,b in p['source']:
        if n=='Qr':
            s += [['ic2','*','i','c2'],['i2','*','ic2','ic2']]
        elif n in ('Q','ic2'):continue
        elif n=='Dm1':s.append(['Dm1','*','A','i2'])
        elif n=='D':
            s.append([n,op,a,b]);s.append(['Q','*','A','Dm1'])
        elif n=='v':s.append(['T2','*','auxiliary_quotient','auxiliary_quotient'])
        elif n=='v2':s.append(['v2','*','c2','T2'])
        elif n=='M':
            s += [['ki2','*','R10b','i2'],['M','+','ki2','T2']]
        else:s.append([n,op,a,b])
    p.update(source=s,name=p['name'].replace('13_','13_lowweight_'))
    if p['name'].startswith('system'):
        p['name']='system13_lowweight79';p['residual_exact_degrees']=[18,7,2,488]
    elif p['name'].startswith('sos'):
        p['name']='sos13_lowweight90';p['exact_degree']=976
    else:
        p['name']='polynomial13_lowweight85';p['exact_degree']=515
    return ledger(p)

def construct14(name):
    p=read(name)
    isouter='outer' in p['name']
    drop={'q_minus_FZ','C_after_alpha','marked_rhs','bound_difference','bound_error',
          'bound_error_square','bound_unit','er_P','ng_bounded_product'}
    aliases={'q_minus_FZ':'alpha','marked_rhs':'C','er_P':'er_P4','ng_bounded_product':'ng_product'}
    source=[]
    for n,op,a,b in p['source']:
        if n in drop: continue
        source.append([n,op,aliases.get(a,a),aliases.get(b,b)])
        if n=='q_minus_F': source.append(['C','-','q_minus_F','alpha'])
    out={k:v for k,v in p.items() if k not in ('degree_upper_by_register','supplementary_full_source_degree_diagnostic','source','ledger','equations')}
    out['witnesses']=[x for x in p['witnesses'] if x!='Z']
    out['fixed_numerals']=[x for x in p['fixed_numerals'] if x not in ('W0','W0plus2d')]
    out.update(source=source,name='outer14_73' if isouter else 'product14_75',
               exact_degree=342 if isouter else 293)
    return ledger(out)

def amalgamate14():
    base=json.loads((HERE.parent/'low_degree'/'ordinary15_system61.json').read_text())
    drop={'tau2','N0','y2','aux_gap','aux_product','Na'}
    s=[row for row in base['source'] if row[0] not in drop]
    s += [['Atau','+','first_product',1],['daux','-','A0',1],
          ['t2','*','t','t'],['leftL','*','daux','t2'],['leftN','*','daux','Atau'],
          ['KV2','*','A0','V2'],['eaux','-','KV2',1],
          ['LNsum','+','leftL','leftN'],['uaux','-','LNsum','eaux'],
          ['uaux2','*','uaux','uaux'],['LNproduct','*','leftL','leftN'],
          ['fourLN','*',4,'LNproduct']]
    p={'name':'amalgam14_system67','source':s,
       'witnesses':[x for x in base['witnesses'] if x not in ('tau','y')]+['t'],
       'fixed_numerals':base['fixed_numerals'],
       'witness_domain':'strictly positive integers',
       'comparisons':[['N1',1],['Nk',1],['Nt',1],['I2','A0'],['uaux2','fourLN']],
       'residual_exact_degrees':[18,7,2,22,72]}
    ledger(p)
    sos=json.loads(json.dumps(p));ss=list(s)
    for j,(a,b) in enumerate(p['comparisons']):
        ss += [[f'res{j}','-',a,b],[f'sq{j}','*',f'res{j}',f'res{j}']]
    ss += [['sum1','+','sq0','sq1'],['sum2','+','sum1','sq2'],['sum3','+','sum2','sq3'],['sos','+','sum3','sq4']]
    sos.pop('comparisons');sos.update(name='amalgam14_sos81',source=ss,output='sos',exact_degree=144)
    ledger(sos)
    prod=json.loads(json.dumps(p));ps=list(s)+[
        ['res','-','uaux2','fourLN'],['guard','+','res',1],
        ['strong_diff','-','I2','A0'],['Ns','+','strong_diff',1],
        ['p2','*','N1','Nk'],['p3','*','p2','Nt'],['p4','*','p3','Ns'],
        ['p5','*','p4','guard'],['polynomial','-','p5',1]]
    prod.pop('comparisons');prod.update(name='amalgam14_product76',source=ps,output='polynomial',exact_degree=121)
    ledger(prod)
    return p,sos,prod

def degree_line(p,seed,prime):
    rng=random.Random(seed)
    vals={v:[rng.randrange(1,17),rng.randrange(1,17)] for v in p['witnesses']}
    vals.update({v:[c] for v,c in zip(p['fixed_numerals'],[31,127,10,45])})
    def plus(a,b,sgn):
        c=[((a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))]
        while len(c)>1 and not c[-1]:c.pop()
        return c
    for n,op,a,b in p['source']:
        a=[a] if type(a) is int else vals[a];b=[b] if type(b) is int else vals[b]
        if op=='*':
            c=[0]*(len(a)+len(b)-1)
            for i,x in enumerate(a):
                for j,y in enumerate(b): c[i+j]=(c[i+j]+x*y)%prime
            while len(c)>1 and not c[-1]:c.pop()
        else:c=plus(a,b,1 if op=='+' else -1)
        vals[n]=c
    if 'output' in p:
        res=[len(vals[p['output']])-1];expect=[p['exact_degree']]
    else:
        res=[len(plus(vals[a] if type(a) is str else [a],vals[b] if type(b) is str else [b],-1))-1 for a,b in p['comparisons']]
        expect=p['residual_exact_degrees']
    assert res==expect,(p['name'],res,expect)
    return {'prime':prime,'seed':seed,'degrees':res}

def independent13(vals,lower_weight=False):
    J,F,alpha,z,filler,h,i,T,s,w,eta,zeta,gamma,t=[vals.get(x) for x in ['Jrep','F','alpha','transport_quotient','f','h','i','auxiliary_quotient','s','w','eta','zeta','gamma','t']]
    m,K,MC,MF=[vals[x] for x in ['Bm1','Kconstant','MC','MF']]
    q=m*J+1;Cw=q-F-alpha;X=w*q;Y=s*q**3;E=X*Y;k=eta+zeta;c=k*Y+eta;a=E+Y;H=4*a+3;Delta=a*a+H
    Dmain=X+a*c+gamma*H
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    Nmain=Dmain**2-Delta*c*c;Nindex=k-h*E-R;Ntrans=(K+w)*Cw+q-F-z*(q-1)
    A=1+(E*k*Y)*(E*k*Y+k);Q=(i*Delta*c*c)**2;D=1+Delta*i*i*c**4
    v=c*T;zroot=c+R*D;Qr=Q-1;M=k*(i*c*c)**2+T*T if lower_weight else D+v*v
    Eroot=Q*(D*v*v+zroot*zroot)-1
    C=Qr*(t*t+M*M*A)-Eroot;B=2*Q*v*zroot
    U=C*C+B*B*D-4*Qr*Qr*t*t*M*M*A
    Froot=U*U-D*(2*C*B)**2
    return [Nmain,Nindex,Ntrans,Froot]

def diagnostic13(p,sos,prod):
    rng=random.Random(130078);count=0
    for _ in range(80):
        values={x:rng.randrange(-3,5) for x in p['witnesses']+p['fixed_numerals']}
        actual=evaluate(p['source'],values)
        truth=independent13(values,lower_weight='lowweight' in p['name'])
        assert [actual['norm_main'],actual['norm_index'],actual['norm_transport'],actual['UU2']-actual['sixteenC2PU']]==truth
        sv=evaluate(sos['source'],values)[sos['output']]
        pv=evaluate(prod['source'],values)[prod['output']]
        assert sv==sum((x-1)**2 for x in truth[:3])+truth[3]**2
        assert pv==truth[0]*truth[1]*truth[2]*(1+truth[3])-1
        count+=1
    return {'independent_formula_assignments':count,'signed_inputs':True,'scope':'Exact algebra diagnostics, no K215 halting or full Pell witness.'}

def root_component_fixtures():
    """Test the exact inverse divisions on isolated square/Pell components."""
    cases=[]
    for s in (2,3,5):
        Q=s*s;d=Q-1
        # chi_s(n), psi_s(n) for odd n; chi_s(n) is divisible by s.
        chi,psi=1,0
        for n in range(1,6):
            chi,psi=s*chi+(s*s-1)*psi,chi+s*psi
            if n not in (3,5):continue
            V=-chi//s
            for f in (-3,2,4):
                D=f*f;v=1;z=v*f-V
                assert z>0 and Q*V*V-d*psi*psi==1
                M=D+v*v
                for sy in (-1,1):
                    y=sy*psi;tau=100*(z+abs(y)+1)
                    A=tau*tau;t=M*tau+y
                    e=Q*(D*v*v+z*z)-1;B=2*Q*v*z
                    C=d*(t*t+M*M*A)-e
                    U=C*C+D*B*B-4*d*d*t*t*M*M*A
                    assert C>0 and U*U-D*(2*C*B)**2==0
                    fr=Fraction(-U,2*C*B)
                    tr=Fraction(C+B*fr,2*d*t*M)
                    yr=t-M*tr
                    assert (fr,tr,yr)==(f,tau,y)
                    cases.append({'sqrt_coefficient':s,'odd_auxiliary_index':n,
                                  'f':f,'y_sign':sy,'inverse_exact':True})
    return {'cases':cases,'count':len(cases),
       'scope':'Isolated root-amalgamation components only, including signed restored f,y; not full source tuples or K215 witnesses.'}

def main():
    p13,sos13,prod13=construct13()
    low=list(map(lower_weight13,(p13,sos13,prod13)))
    ps=[p13,sos13,prod13,*low,construct14('p82_source.json'),construct14('p80_source.json'),*amalgamate14()]
    check=diagnostic13(p13,sos13,prod13)
    receipt={'coefficient_binding':COEFFICIENT_BINDING,'diagnostic13':check,'diagnostic13_lowweight':diagnostic13(*low),'root_component_fixtures':root_component_fixtures(),'packets':{}}
    for p in ps:
        p['coefficient_binding']=COEFFICIENT_BINDING
        diagnostics=[degree_line(p,8371,1000000007),degree_line(p,8372,1000000009)]
        p['degree_diagnostics']=diagnostics
        write(p['name']+'.json',p)
        receipt['packets'][p['name']]={'variables':len(p['witnesses']),'ledger':p['ledger'],'degree_diagnostics':diagnostics}
    write('candidate_receipt.json',receipt)
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()

