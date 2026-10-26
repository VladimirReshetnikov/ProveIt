#!/usr/bin/env python3
"""Independent finite verification of the compact supplement.

This checker imports no circuit producer or coefficient constructor.
It uses only the retained generic sparse integer polynomial helper.
"""
from pathlib import Path
from collections import Counter
import copy, gzip, hashlib, importlib.util, json

ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('poly', ROOT/'163-trace-radical/compact/polynomial.py')
poly=importlib.util.module_from_spec(spec);spec.loader.exec_module(poly)
Poly,require=poly.Poly,poly.require
INPUTS=['J','F','alpha','i','T','w','s','n','eta','zeta']
PORTS=['beta','K0','MC','MF']

def topology(g):
    require(g['domain']=='strictly positive integers','domain')
    require(g['witnesses']==INPUTS and g['fixed_numerals']==PORTS,'inputs/ports')
    available=set(INPUTS+PORTS);defs={}
    for n,op,a,b in g['source']:
        require(n not in available and op in ('+','-','*'),'DAG definition')
        require(all(type(x)==int or x in available for x in (a,b)),'DAG order')
        available.add(n);defs[n]=(a,b)
    live=set()
    def visit(x):
        if type(x)==int or x in live:return
        live.add(x)
        if x in defs:
            for y in defs[x]:visit(y)
    visit(g['output'])
    require(live==available,'all nodes/ports/inputs live')
    require(g['operations']==len(g['source']),'operation count')
    require(g['operation_breakdown']==dict(Counter(r[1] for r in g['source'])),'operation classes')

def cuts(g):
    definitions={r[0]:r[1:] for r in g['source']}
    boundary={n:Poly.v(n) for n in INPUTS+PORTS};used=set();receipts=[]
    def expand(n,memo):
        if type(n)==int:return Poly(n)
        if n in boundary:return boundary[n]
        if n in memo:return memo[n]
        op,a,b=definitions[n];used.add(n)
        x,y=expand(a,memo),expand(b,memo)
        memo[n]=x+y if op=='+' else x-y if op=='-' else x*y
        return memo[n]
    def cut(n,expected):
        value=expand(n,{})
        require(value==expected,'polynomial cut '+n)
        receipts.append({'register':n,'monomials':len(value.d)})
        boundary[n]=Poly.v(n)
    p=boundary.__getitem__
    cut('bJ',p('beta')*p('J'));cut('q',p('bJ')+1)
    cut('q2',p('q')**2);cut('q4',p('q2')**2);cut('q6',p('q4')*p('q2'));cut('sixq6',6*p('q6'))
    cut('Y',p('q')*p('s'));cut('qmF',p('q')-p('F'));cut('C',p('qmF')-p('alpha'))
    cut('X',p('q')*p('w'));cut('k',p('eta')+p('zeta'));cut('c',p('k')*p('Y')+p('eta'))
    cut('XY',p('X')*p('Y'));cut('Am1',p('XY')+p('Y'));cut('Hp',4*p('Am1')-1);cut('Ap1',p('Am1')+2)
    cut('V0k',p('XY')*p('k')*p('Y'))
    cut('Dtau',1+p('V0k')*(p('V0k')+p('k')))
    cut('R',(p('bJ')*p('qmF')+p('alpha'))*(p('q2')-1)+(p('MC')+p('q')*p('MF'))*p('J'))
    cut('eclear',6*(p('k')-p('R')-1-p('q4')*p('s'))-p('V0k')*(p('k')**2-4))
    cut('Bt',(p('K0')+p('w'))*p('C')-p('F'))
    cut('U',p('i')*p('c')**2);cut('Delta',p('Am1')*p('Ap1'))
    cut('DpI2',p('Delta')*p('U')**2*p('Dtau'));cut('Df',1+p('DpI2'))
    cut('trace_f',p('DpI2')+p('Df'));cut('Q',4*p('Delta')*p('DpI2')*p('Df'))
    cut('cTR',p('c')*p('T')-p('R'));cut('V',p('trace_f')*p('cTR')-p('c'));cut('V2',p('V')**2)
    cut('Kpos',p('X')*(3*p('c')-2*p('X'))+2)
    weight=p('cTR')**2 if g['transport_weight']=='b2' else p('cTR')*p('V')
    cut('Znum',p('bJ')*p('sixq6')*(p('Hp')*(p('n')-weight*p('Bt'))+p('Kpos'))-p('Hp')*(p('sixq6')*p('Bt')+p('bJ')*p('eclear')))
    cut('Mtot',p('bJ')*p('sixq6')*p('Hp'));cut('Dg',p('Dtau')*p('Df'))
    output_carrier=p('Znum')
    if g['name']=='centered224':
        cut('Zshift',p('Znum')-p('Mtot')*(p('Am1')+1)*p('U')*p('Dtau')*p('V'))
        output_carrier=p('Zshift')
    rg=p('Mtot')**2*p('Dg')
    cut('N',p('Q')*(output_carrier**2-rg*p('V2'))+rg-output_carrier**2)
    require(used==set(definitions),'coverage of every actual gate')
    return receipts

def identities():
    A,U,E,Q,M,V,Z=map(Poly.v,['A','U','E','Q','M','V','Z'])
    C=A*U*E;G=E*(1+(A*A-1)*U*U*E)
    require(C*C-G==E*(U*U*E-1),'root gap identity')
    old=(Q-1)*(Z-M*C*V)**2-M*M*G*(Q*V*V-1)
    expanded=(Q-1)*Z*Z-2*(Q-1)*M*C*V*Z+M*M*V*V*(Q*E*(U*U*E-1)-C*C)+M*M*G
    require(old==expanded,'complete centered norm identity')
    require((Q-1)*C*C-Q*G==Q*E*(U*U*E-1)-C*C,'slope identity')
    return 3

def leading(g):
    env={v:(1,Poly.v(v)) for v in INPUTS};env.update({v:(0,Poly.v(v)) for v in PORTS})
    def get(x):return (0,Poly(x)) if type(x)==int else env[x]
    rows=[];centered=g['name']=='centered224'
    for n,op,a,b in g['source']:
        da,x=get(a);db,y=get(b)
        if op=='*':d,top=da+db,x*y
        elif da>db:d,top=da,x
        elif db>da:d,top=db,y if op=='+' else -y
        else:d,top=da,x+y if op=='+' else x-y
        require(bool(top.d),'unresolved cancellation '+n)
        env[n]=(d,top);rows.append({'register':n,'degree':d,'top_monomials':len(top.d)})
        if centered and n=='Zshift':break
    q=Poly.v('beta')*Poly.v('J');k=Poly.v('eta')+Poly.v('zeta')
    w,s,i,T,F=map(Poly.v,['w','s','i','T','F']);B=k*s*T-q*q*(q-F)
    if centered:
        expected=9*2**10*q**96*w**24*s**56*i**10*k**32*B**2
        ds={n:env[n][0] for n in ['Q','Mtot','V','U','Dtau','Znum','root_center','Dg']}
        require(ds=={'Q':80,'Mtot':11,'V':40,'U':7,'Dtau':14,'Znum':21,'root_center':25,'Dg':50},'center degrees')
        degree=2*ds['Mtot']+2*ds['V']+ds['Q']+2*ds['U']+2*ds['Dtau']
        top=env['Mtot'][1]**2*env['V'][1]**2*env['Q'][1]*env['U'][1]**2*env['Dtau'][1]**2
        # Exact identity above bounds all other summands strictly below224.
        lower=[ds['Q']+2*ds['Znum'],ds['Q']+ds['Mtot']+ds['root_center']+ds['V']+ds['Znum'],2*ds['Mtot']+2*ds['V']+2*ds['root_center'],2*ds['Mtot']+ds['Dg'],2*ds['Mtot']+2*ds['V']+ds['Q']+ds['Dtau']]
        require(max(lower)<224,'separation from every lower summand')
    else:
        expected=-9*2**10*q**100*w**26*s**58*i**10*k**32*B**2
        degree,top=env[g['output']]
    require(top==expected and degree==g['exact_degree'],'exact complete leading form')
    return {'degree':degree,'top':top.serial(),'registers':rows}

def coefficients(g):
    answer=[]
    for name,p in g['coefficient_binding']['ports'].items():
        data=(ROOT/g['coefficient_binding']['path']/p['file']).read_bytes();raw=gzip.decompress(data)
        require(hashlib.sha256(raw).hexdigest()==p['raw_sha256'],'raw coefficient '+name)
        require(hashlib.sha256(data).hexdigest()==p['gzip_sha256'],'compressed coefficient '+name)
        require(int.from_bytes(raw,'little').bit_length()==p['bits'],'coefficient bits '+name)
        answer.append({'port':name,'bits':p['bits'],'sha256':p['raw_sha256']})
    return answer

def main():
    result={'identities':identities(),'equations':[]}
    for path in sorted((ROOT/'compact_equations').glob('*.json')):
        g=json.loads(path.read_text());topology(g);c=cuts(g);l=leading(g);ports=coefficients(g);rejected=0
        for j,row in enumerate(g['source']):
            for op in ('+','-','*'):
                if op==row[1]:continue
                altered=copy.deepcopy(g);altered['source'][j][1]=op
                try:cuts(altered)
                except (ValueError,KeyError):rejected+=1
                else:raise ValueError(('operator corruption survived',path.name,row[0],op))
        result['equations'].append({'file':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'operations':len(g['source']),'degree':l['degree'],'cuts':c,'leading':l,'coefficients':ports,'corruptions_rejected':rejected})
    (ROOT/'COMPACT_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'identities':result['identities'],'equations':[{k:r[k] for k in ('file','operations','degree','corruptions_rejected')} for r in result['equations']]},indent=2))

if __name__=='__main__':main()
