#!/usr/bin/env python3
"""Independent exact cuts, full homogeneous forms, and fixed-numeral recipe.
No producer import. Sparse ring arithmetic is retained with its attribution.
"""
from pathlib import Path
from collections import Counter
import argparse, copy, gzip, hashlib, importlib.util, json
from polynomial import Poly
ROOT=Path(__file__).resolve().parent
INPUTS=['J','F','alpha','i','T','w','s','n','eta','zeta']
PORTS=['beta','K0','MC','MF']
SPECS={'free_plain':(82,240),'scaled_inverse':(85,232),'free_inverse':(87,214)}
def need(ok,msg):
    if not ok:raise ValueError(msg)
def cuts(mode):
    scaled=mode=='scaled_inverse';plain=mode=='free_plain';dn='D' if plain else 'sixq6' if scaled else 'sixq7'
    v={'q':'beta*J+1','C':'q-F-alpha','X':'q*q*w' if plain else 'q*w','k':'eta+zeta',
      'c':'k*q*s+eta' if scaled else 'k*s+eta','Am1':'q*s*(X+1)','Hp':'4*Am1-1',
      'Delta':'Am1*(Am1+2)',dn:'q**7' if plain else '6*q**6' if scaled else '6*q**7',
      'Dtau':'1+(X*q*q*s*s)*(X*q*q*s*s+1)*k*k',
      'R':'(bJ*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J',
      'Bt':'(K0+q*w)*C-F' if plain else '(K0+w)*C-F',
      'U':'i*c*c','DpI2':'Delta*U*U*Dtau','Df':'DpI2+1','trace_f':'1+2*DpI2',
      'Q':'4*Delta*DpI2*(1+DpI2)','cTR':'c*T-R','V':'trace_f*cTR-c',
      'Kpos':'X*(3*c-2*X)+2','Dg':'Dtau*Df','Mtot':f'bJ*{dn}*Hp','RG':'Mtot*Mtot*Dg',
      'eclear':'k-R-1-q**4*s' if plain else '6*(k-R-1-q**4*s)-(X*q*q*s*s)*k*(k*k-4)',
      'Znum':f'bJ*{dn}*(Hp*(n-cTR*V*Bt)+Kpos)-Hp*({dn}*Bt+bJ*eclear)',
      'N':'Q*(Znum*Znum-Mtot*Mtot*Dg*V*V)+(Mtot*Mtot*Dg-Znum*Znum)'}
    return v

def topology_and_cuts(g,mode):
    need(g['domain']=='strictly positive integers','domain');need(g['witnesses']==INPUTS,'inputs');need(g['fixed_numerals']==PORTS,'ports')
    table={};known=set(INPUTS+PORTS)
    for name,op,a,b in g['source']:
        need(name not in known,'duplicate register');need(op in ['+','-','*'],'operation')
        need(all(type(x)is int or x in known for x in [a,b]),'operand')
        table[name]=(op,a,b);known.add(name)
    live=set()
    def mark(x):
        if type(x)is int or x in live:return
        live.add(x)
        if x in table:
            _,a,b=table[x];mark(a);mark(b)
    mark(g['output']);need(live==known,'liveness')
    opcounts=dict(sorted(Counter(r[1] for r in g['source']).items()))
    need(len(table)==SPECS[mode][0]==g['operations'],'op count');need(opcounts==g['operation_breakdown'],'op classes')
    covered=set();receipt=[]
    import ast
    for name,formula in cuts(mode).items():
        names={n.id for n in ast.walk(ast.parse(formula,mode='eval')) if isinstance(n,ast.Name)}
        env={n:Poly.v(n) for n in names};memo=env.copy()
        def expand(x):
            if type(x)is int:return Poly(x)
            if x in memo:return memo[x]
            need(x in table,'unbound cut '+x);covered.add(x)
            op,a,b=table[x];a,b=expand(a),expand(b)
            out=a+b if op=='+' else a-b if op=='-' else a*b;memo[x]=out;return out
        got=expand(name);expect=eval(formula,{'__builtins__':{}},env)
        need(got==expect,'free-ring cut '+name)
        receipt.append({'register':name,'terms':len(got.d)})
    need(covered==set(table),'uncovered gates '+str(set(table)-covered))
    return {'operations':len(table),'operation_counts':opcounts,'all_gates_covered':True,'cuts':receipt}

def leading(g,mode):
    values={n:(1 if n in INPUTS else 0,Poly.v(n)) for n in INPUTS+PORTS};ledger={}
    def get(x):return (0,Poly(x)) if type(x)is int else values[x]
    for name,op,a,b in g['source']:
        da,a=get(a);db,b=get(b)
        if op=='*':d,p=da+db,a*b
        elif da==db:d,p=da,a+b if op=='+' else a-b
        elif da>db:d,p=da,a
        else:d,p=db,b if op=='+' else -b
        need(bool(p.d),'cancelled leading form '+name);values[name]=(d,p)
        ledger[name]={'degree':d,'form':p.serial()}
    q=Poly.v('beta')*Poly.v('J');k=Poly.v('eta')+Poly.v('zeta');w,s,i,T,F=[Poly.v(n) for n in ['w','s','i','T','F']]
    if mode=='free_plain':coef,ex,rest=-256,112,q-F
    elif mode=='free_inverse':coef,ex,rest=-9216,86,q-F
    else:coef,ex,rest=-9216,100,k*s*T-q*q*(q-F)
    expected=coef*q**ex*w**26*s**58*i**10*k**32*rest**2
    d,p=values[g['output']];need(d==SPECS[mode][1]==g['exact_degree'],'exact degree');need(p==expected,'full top form')
    return {'exact_degree':d,'top_form':expected.serial(),'top_terms':len(expected.d),'all_register_top_forms':ledger}

def identities():
    # The e*-d cubic identity, after t=2m, k-t=8v A_m and k=t+8v A_m.
    v,t,A,Z=[Poly.v(n) for n in ['v','t','A','Z']];k=t+8*v*A
    # 48 C_m=t(t²−4), A=C_m+4vZ -> 48A=t(t²−4)+192vZ.
    # Universal identity valid after eliminating C_m, with a factor48 to avoid fractions.
    # Direct cleared form: 6(e*-d)=6(k-t)-v*k(k²−4).
    target=6*(k-t)-v*k*(k*k-4)
    rhs=8*v*v*(24*Z-A*(k*k+k*t+t*t-4))
    # Difference equals v*(48A-t(t²−4)-192vZ), the named recurrence relation.
    need(target-rhs==v*(48*A-t*(t*t-4)-192*v*Z),'inverse difference identity')
    c,d,R,T,f=[Poly.v(n) for n in ['c','d','R','T','f']]
    ff=1+c*d;Tnew=ff*T-d*R
    need(ff*(c*Tnew-R)-c==ff*ff*(c*T-R)-c,'linear trace substitution')
    Q,Zn,M,G,V=[Poly.v(n) for n in ['Q','Zn','M','G','V']]
    need(Q*(Zn*Zn-M*M*G*V*V)+(M*M*G-Zn*Zn)==(Q-1)*Zn*Zn-M*M*G*(Q*V*V-1),'norm identity')
    return {'inverse_cubic_cleared_identity':True,'trace_polynomial_map':True,'norm_identity':True}

def authenticate(g,deep):
    parent=g['parent'];need(hashlib.sha256((ROOT/parent['path']).read_bytes()).hexdigest()==parent['sha256'],'parent pin')
    vals={};binding=g['coefficient_binding']
    need(binding['byte_order']=='big','byte order')
    cert=ROOT/binding['certificate'];need(hashlib.sha256(cert.read_bytes()).hexdigest()==binding['certificate_sha256'],'certificate pin')
    need(set(binding['ports'])==set(PORTS),'entire four-port tuple')
    for name,pin in binding['ports'].items():
        raw=(ROOT/binding['path']/pin['file']).read_bytes()
        need(hashlib.sha256(raw).hexdigest()==pin['sha256'],'raw numeral '+name)
        vals[name]=int.from_bytes(raw,'big');need(vals[name].bit_length()==pin['bits'],'bits '+name)
        need(len(raw)==pin['bytes'],'bytes '+name)
    need(vals['beta']==2**193969-1,'exact new beta')
    need(sum(x['bytes'] for x in binding['ports'].values())==97046,'whole tuple size')
    need(0<vals['MC']<vals['beta']<vals['MF']<2*vals['beta'],'scalar boxes')
    if deep:
        # Independent finite reconstruction imports NO producer.
        from verify_native import run
        audit=run('4127')
        for name in PORTS:need(audit['port_sha256'][name]==binding['ports'][name]['sha256'],'independent tuple hash '+name)
        return {'whole_tuple_independently_reconstructed':True,'native_audit':audit}
    return {'coefficient_payloads_authenticated':True}

def mutations(g,mode):
    count=0
    for idx,row in enumerate(g['source']):
        for op in ['+','-','*']:
            if op==row[1]:continue
            bad=copy.deepcopy(g);bad['source'][idx][1]=op
            bad['operation_breakdown']=dict(sorted(Counter(r[1] for r in bad['source']).items()))
            try:topology_and_cuts(bad,mode)
            except (ValueError,KeyError):count+=1
            else:raise ValueError('accepted mutation '+row[0]+':'+op)
    return count

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);ap.add_argument('--deep',action='store_true');ap.add_argument('--mutations',action='store_true');a=ap.parse_args()
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())['dependencies']
    for rel,pin in pins.items():
        raw=(ROOT/rel).read_bytes();need(len(raw)==pin['bytes'] and hashlib.sha256(raw).hexdigest()==pin['sha256'],'source pin '+rel)
    result={'status':'PASS','authenticated_source_files':len(pins),'identities':identities(),'equations':[]}
    for mode,(ops,deg) in SPECS.items():
        path=ROOT/f'start4127_positive10_degree{deg}_ops{ops}.json';g=json.loads(path.read_text())
        record={'name':g['name'],'mode':mode,'formulas':topology_and_cuts(g,mode),'degree':leading(g,mode),'coefficients':authenticate(g,a.deep)}
        if a.mutations:record['rejected_operator_mutations']=mutations(g,mode)
        result['equations'].append(record)
    if a.receipt:a.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','equations':[{'name':r['name'],'degree':r['degree']['exact_degree'],'operations':r['formulas']['operations'],'top_terms':r['degree']['top_terms'],'mutations':r.get('rejected_operator_mutations')} for r in result['equations']]},indent=2))
if __name__=='__main__':main()
