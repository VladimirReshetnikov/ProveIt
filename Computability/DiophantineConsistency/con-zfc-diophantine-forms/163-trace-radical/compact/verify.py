#!/usr/bin/env python3
"""Independent finite checks of the supplied trace-linear equations.

The expected formulas and full leading forms are specified here, separately
from the producer. The inherited sparse arithmetic helper is attributed in
polynomial.py. No producer or inherited verifier is imported.
"""
from pathlib import Path
from collections import Counter
import argparse, copy, gzip, hashlib, json
from polynomial import Poly, require

ROOT=Path(__file__).resolve().parent
INPUTS=['J','F','alpha','i','T','w','s','n','eta','zeta']
PORTS=['beta','K0','MC','MF']

def topology(g):
    require(g['domain']=='strictly positive integers','domain')
    require(g['witnesses']==INPUTS,'unknowns')
    require(g['fixed_numerals']==PORTS,'ports')
    available=set(INPUTS+PORTS); defs={}
    for name,op,a,b in g['source']:
        require(name not in available,'duplicate')
        require(op in ('+','-','*'),'operation')
        for x in (a,b): require(type(x)==int or x in available,'missing operand')
        defs[name]=(a,b); available.add(name)
    live=set()
    def visit(x):
        if type(x)==int or x in live:return
        live.add(x)
        if x in defs:
            for y in defs[x]:visit(y)
    visit(g['output'])
    require(live==available,'dead input, port or operation')
    ops=dict(Counter(r[1] for r in g['source']))
    require(g['operations']==len(g['source']),'count')
    require(g['operation_breakdown']==ops,'operation classes')
    return ops

def cuts(g):
    definitions={r[0]:r[1:] for r in g['source']}
    boundary={n:Poly.v(n) for n in INPUTS+PORTS}; used=set(); receipts=[]
    def expand(n,memo):
        if type(n)==int:return Poly(n)
        if n in boundary:return boundary[n]
        if n in memo:return memo[n]
        op,a,b=definitions[n]; used.add(n)
        x,y=expand(a,memo),expand(b,memo)
        memo[n]=x+y if op=='+' else x-y if op=='-' else x*y
        return memo[n]
    def cut(n,expected):
        result=expand(n,{})
        require(result==expected,'polynomial cut '+n)
        receipts.append({'register':n,'terms':len(result.d)})
        boundary[n]=Poly.v(n)
    p=boundary.__getitem__; chart=g['chart']
    cut('bJ',p('beta')*p('J'));cut('q',p('bJ')+1)
    cut('q2',p('q')**2)
    if chart=='q3':cut('q3',p('q2')*p('q'))
    else:cut('q4',p('q2')**2)
    if chart=='lucas':
        cut('q6',p('q4')*p('q2'));cut('sixq6',6*p('q6'))
    if chart=='q2':cut('D',p('q4')*p('q'))
    if chart=='q1':cut('D',p('q4')*p('q2'))
    yn={'q3':'q3','q2':'q2','q1':'q','lucas':'q'}[chart]
    cut('Y',p(yn)*p('s'));cut('qmF',p('q')-p('F'))
    cut('C',p('qmF')-p('alpha'))
    if chart=='q1':
        cut('Wbase',p('q')*p('w'));cut('X',p('q')*p('Wbase'))
        W=p('Wbase')
    else:cut('X',p('w')*p('q'));W=p('w')
    cut('k',p('eta')+p('zeta'));cut('c',p('k')*p('Y')+p('eta'))
    cut('XY',p('X')*p('Y'))
    if chart=='lucas':cut('v0',p('XY')*p('Y'))
    cut('Am1',p('XY')+p('Y'));cut('Hp',4*p('Am1')-1)
    cut('Ap1',p('Am1')+2)
    v=p('v0') if chart=='lucas' else p('XY')*p('Y')
    cut('Dtau',1+v*(v+1)*p('k')**2)
    cut('R',(p('bJ')*p('qmF')+p('alpha'))*(p('q2')-1)+(p('MC')+p('q')*p('MF'))*p('J'))
    if chart=='lucas':
        cut('Rp1',p('R')+1);cut('e',p('k')-p('Rp1'))
        cut('eclear',6*(p('e')-p('q4')*p('s'))-p('v0')*p('Rp1')*(p('Rp1')**2-4))
    else:cut('e',p('k')-p('R')-1)
    if chart in ('q1','q2'):cut('eclear',p('e')-p('s')*p('q4'))
    cut('Bt',(p('K0')+W)*p('C')-p('F'))
    cut('U',p('i')*p('c')**2);cut('Delta',p('Am1')*p('Ap1'))
    cut('DpI2',p('Delta')*p('U')**2*p('Dtau'))
    cut('Df',1+p('DpI2'));cut('trace_f',p('DpI2')+p('Df'))
    cut('Q',4*p('Delta')*p('DpI2')*p('Df'))
    cut('cTR',p('c')*p('T')-p('R'))
    cut('V',p('trace_f')*p('cTR')-p('c'));cut('V2',p('V')**2)
    cut('Kpos',p('X')*(3*p('c')-2*p('X'))+2)
    den=p('XY') if chart=='q3' else p('sixq6') if chart=='lucas' else p('D')
    error=p('e') if chart=='q3' else p('eclear')
    weight=p('V2') if g['transport_weight']=='V2' else p('cTR')*p('V')
    cut('Znum',p('bJ')*den*(p('Hp')*(p('n')-weight*p('Bt'))+p('Kpos'))-p('Hp')*(den*p('Bt')+p('bJ')*error))
    cut('Mtot',p('bJ')*den*p('Hp'));cut('Dg',p('Dtau')*p('Df'))
    rg=p('Mtot')**2*p('Dg')
    cut('N',p('Q')*(p('Znum')**2-rg*p('V2'))+rg-p('Znum')**2)
    require(used==set(definitions),'uncovered actual gates')
    return receipts

def leading(g):
    env={v:(1,Poly.v(v)) for v in INPUTS}
    env.update({v:(0,Poly.v(v)) for v in PORTS})
    def get(x):return (0,Poly(x)) if type(x)==int else env[x]
    rows=[]
    for n,op,a,b in g['source']:
        da,x=get(a);db,y=get(b)
        if op=='*':d,top=da+db,x*y
        elif da>db:d,top=da,x
        elif db>da:d,top=db,y if op=='+' else -y
        else:d,top=da,x+y if op=='+' else x-y
        require(bool(top.d),'complete top cancellation at '+n)
        env[n]=(d,top);rows.append({'register':n,'degree':d,'terms':len(top.d)})
    q=Poly.v('beta')*Poly.v('J');k=Poly.v('eta')+Poly.v('zeta')
    w,s,i,T,F,alpha=(Poly.v(x) for x in ('w','s','i','T','F','alpha'))
    C=q-F-alpha;B=k*s*T-q*q*(q-F)
    if g['chart']=='lucas':expected=-9*2**10*q**100*w**26*s**58*i**10*k**32*B**2
    elif g['chart']=='q1':expected=-2**8*q**126*w**26*s**58*i**10*k**32*B**2
    elif g['chart']=='q2':expected=-2**8*q**158*w**26*s**60*i**10*k**34*T**2
    elif g['transport_weight']=='bV':expected=-2**8*q**216*w**28*s**62*i**10*k**34*T**2
    else:expected=2**10*q**242*w**32*s**70*i**12*k**40*T**4*C**2
    degree,top=env[g['output']]
    require(degree==g['exact_degree'],'exact degree')
    require(top==expected,'full highest homogeneous part')
    # Every coefficient of the top form is supplied, not a ray test.
    return {'degree':degree,'top':top.serial(),'registers':rows}

def identities():
    Delta,U,E,c,T,R=map(Poly.v,('Delta','U','E','c','T','R'))
    a=Delta*U**2*E;f=1+2*a;F0=1+a;G=E*F0
    require(f*f-1==4*a*F0,'doubled trace')
    require(Delta*(f*f-1)==4*Delta**2*U**2*G,'product-square factor')
    i=Poly.v('i');a=Delta*i**2*c**4*E;f=1+2*a
    require(f-1==c*(2*Delta*i*i*c**3*E),'literal trace congruence')
    V=f*(c*T-R)-c
    require(V+R==c*(f*T-1-2*Delta*i*i*c**3*E*R),'new c residue')
    Q=Delta*(f*f-1);c3=4*Delta+3;b=Poly.v('b')
    require(f*b-c-(4*Q-3)==f*(b-4*Delta*f)-(c-c3),'positive third-index exclusion')
    require(f*b-c+(4*Q-3)==f*(b+4*Delta*f)-(c+c3),'negative third-index exclusion')
    Tnew=f*T-(2*Delta*i*i*c**3*E)*R
    require(c*Tnew-R==f*(c*T-R),'canonical auxiliary transport')
    old_b=c*T-R;new_b=c*Tnew-R
    old_V=f*f*old_b-c;new_V=f*new_b-c
    require(old_V==new_V,'whole old/new auxiliary polynomial')
    # The rest of P depends on T and n only through V and n-LB.
    # Check both carrier substitutions in a free ring at these interfaces.
    ff,bb,vv,nn,BB=map(Poly.v,('f','b','V','n','B'))
    old_L=bb*vv;new_L=ff*old_L
    new_n=nn+(ff-1)*old_L*BB
    require(new_n-new_L*BB==nn-old_L*BB,'bV whole carrier pullback')
    return 9

def coefficient_binding(g):
    values={};result=[]
    for port,item in g['coefficient_binding']['ports'].items():
        data=(ROOT/g['coefficient_binding']['path']/item['file']).read_bytes()
        raw=gzip.decompress(data);value=int.from_bytes(raw,'little')
        require(hashlib.sha256(data).hexdigest()==item['gzip_sha256'],'compressed numeral '+port)
        require(hashlib.sha256(raw).hexdigest()==item['raw_sha256'],'numeral '+port)
        require(value.bit_length()==item['bits'],'numeral length '+port)
        values[port]=value;result.append({'port':port,'bits':value.bit_length(),'sha256':item['raw_sha256']})
    require(values['beta']>=31 and values['beta']%2==1 and values['K0']>0,'port bounds')
    require(0<values['MC']<values['beta']<values['MF']<2*values['beta'],'mask bounds')
    return result

def check_parent_delta(g):
    parent_path=ROOT/g['parent']['path'];data=parent_path.read_bytes()
    require(hashlib.sha256(data).hexdigest()==g['parent']['sha256'],'parent hash')
    old=json.loads(data);new=copy.deepcopy(g['source']);recovered=[]
    require([r[0] for r in old['source'] if 'Fsqr' in r[2:]]==['DfcTR'],'the only discarded-square consumer is the auxiliary product')
    for row in new:
        if row[0]=='twice_a':continue
        if row[0]=='trace_f':recovered.append(['Fsqr','+','fouraF0',1]);continue
        recovered.append([row[0],row[1]]+['Fsqr' if x=='trace_f' else x for x in row[2:]])
    require(recovered==old['source'],'entire parent/child gate relation')
    for port in PORTS:
        require(g['coefficient_binding']['ports'][port]['raw_sha256']==old['coefficient_binding']['ports'][port]['raw_sha256'],'whole tuple continuity')
    return {'old_operations':len(old['source']),'old_degree':old['exact_degree']}

def mutation_controls(g):
    rejected=0
    for target in ('trace_f','Q','V','U','Dtau','R','Znum','Mtot','N'):
        for changed_op in ('+','-','*'):
            mutant=copy.deepcopy(g)
            row=next(r for r in mutant['source'] if r[0]==target)
            if row[1]==changed_op:continue
            row[1]=changed_op
            try:cuts(mutant)
            except (ValueError,KeyError):rejected+=1
            else:raise ValueError('undetected operator mutation: '+target)
    return rejected

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);args=ap.parse_args()
    pins=json.loads((ROOT/'SOURCE_LEDGER.json').read_text())
    for item in pins['sources']:
        require(hashlib.sha256((ROOT/item['local']).read_bytes()).hexdigest()==item['sha256'],'source pin '+item['local'])
    result={'algebraic_identities':identities(),'source_files_authenticated':len(pins['sources']),'circuits':[]}
    for path in sorted((ROOT/'equations').glob('*.json')):
        g=json.loads(path.read_text())
        result['circuits'].append({'file':str(path.relative_to(ROOT)),
            'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'operations':g['operations'],'operation_classes':topology(g),
            'parent':check_parent_delta(g),'cuts':cuts(g),'leading':leading(g),
            'coefficients':coefficient_binding(g),'rejected_corruptions':mutation_controls(g)})
    if args.receipt:args.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'identities':result['algebraic_identities'],'source_files':len(pins['sources']),
        'circuits':[{'file':r['file'],'operations':r['operations'],'degree':r['leading']['degree'],
            'cuts':len(r['cuts']),'top_terms':len(r['leading']['top']),
            'corruptions_rejected':r['rejected_corruptions']} for r in result['circuits']]},indent=2))

if __name__=='__main__':main()
