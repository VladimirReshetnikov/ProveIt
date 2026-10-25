#!/usr/bin/env python3
"""Independent exact cuts, global leading forms, and finite Lucas controls.

No producer is imported. Sparse polynomial arithmetic is credited to and
retained from the earlier parent verifier; all expected new formulas below
are stated separately from build.py and its row edits.
"""
from pathlib import Path
from collections import Counter
import copy, gzip, hashlib, importlib.util, json, math, sys
sys.dont_write_bytecode=True

ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('credited_parent_polynomial_arithmetic',ROOT/'inherited_lucas'/'parent'/'verify.py')
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
Poly=module.Poly

def require(ok,message):
    if not ok:raise ValueError(message)

def topology(g):
    available=set(g['witnesses'])|set(g['fixed_numerals'])
    for name,op,a,b in g['source']:
        require(name not in available,'duplicate '+name)
        require(op in ('+','-','*'),'operation')
        for x in (a,b):require(type(x)==int or x in available,'undefined operand '+str(x))
        available.add(name)
    defs={r[0]:r[2:] for r in g['source']};live=set()
    def visit(x):
        if type(x)==int or x in live:return
        live.add(x)
        if x in defs:
            for y in defs[x]:visit(y)
    visit(g['output'])
    require(live==available,'dead row or input')
    ops=Counter(r[1] for r in g['source'])
    require(sum(ops.values())==g['operations'],'operation count')
    require(dict(ops)==g['operation_breakdown'],'operation breakdown')
    require(g['witnesses']==['J','F','alpha','i','T','w','s','n','eta','zeta'],'ten inputs')
    require(g['fixed_numerals']==['beta','K0','MC','MF'],'four fixed ports')
    return dict(ops)

def exact_cuts(g):
    defs={r[0]:r[1:] for r in g['source']}
    boundary={n:Poly.v(n) for n in g['witnesses']+g['fixed_numerals']}
    used=set();receipts=[]
    def expand(name,memo):
        if type(name)==int:return Poly(name)
        if name in boundary:return boundary[name]
        if name in memo:return memo[name]
        op,a,b=defs[name];used.add(name)
        x,y=expand(a,memo),expand(b,memo)
        ans=x+y if op=='+' else x-y if op=='-' else x*y
        memo[name]=ans;return ans
    def cut(name,expected):
        got=expand(name,{})
        require(got==expected,'exact polynomial cut '+name)
        boundary[name]=Poly.v(name)
        receipts.append({'register':name,'terms':len(got.d)})
    p=boundary.__getitem__
    cut('bJ',p('beta')*p('J'))
    cut('q',p('bJ')+1)
    cut('q2',p('q')**2)
    cut('q4',p('q2')**2)
    cut('q6',p('q4')*p('q2'))
    cut('sixq6',6*p('q6'))
    cut('Y',p('q')*p('s'))
    cut('qmF',p('q')-p('F'))
    cut('C',p('qmF')-p('alpha'))
    cut('X',p('w')*p('q'))
    cut('k',p('eta')+p('zeta'))
    cut('c',p('k')*p('Y')+p('eta'))
    cut('XY',p('X')*p('Y'))
    cut('V0k',p('XY')*p('Y')*p('k'))
    cut('Am1',p('XY')+p('Y'))
    cut('Hp',4*p('Am1')-1)
    cut('Ap1',p('Am1')+2)
    cut('Dtau',1+p('V0k')*(p('V0k')+p('k')))
    cut('R',(p('bJ')*p('qmF')+p('alpha'))*(p('q2')-1)+(p('MC')+p('q')*p('MF'))*p('J'))
    cut('Rp1',p('R')+1)
    cut('e',p('k')-p('Rp1'))
    cut('eclear',6*(p('e')-p('q4')*p('s'))-p('V0k')*(p('k')**2-4))
    cut('Bt',(p('K0')+p('w'))*p('C')-p('F'))
    cut('U',p('i')*p('c')**2)
    cut('Delta',p('Am1')*p('Ap1'))
    cut('DpI2',p('Delta')*p('U')**2*p('Dtau'))
    cut('Df',1+p('DpI2'))
    cut('Fsqr',1+4*p('DpI2')*p('Df'))
    cut('Q',4*p('Delta')*p('DpI2')*p('Df'))
    cut('cTR',p('c')*p('T')-p('R'))
    cut('V',p('Fsqr')*p('cTR')-p('c'))
    cut('V2',p('V')**2)
    cut('Kpos',p('X')*(3*p('c')-2*p('X'))+2)
    weight=p('V2') if g['transport_weight']=='V2' else p('cTR')*p('V')
    cut('Znum',p('bJ')*p('sixq6')*(p('Hp')*(p('n')-weight*p('Bt'))+p('Kpos'))-p('Hp')*(p('sixq6')*p('Bt')+p('bJ')*p('eclear')))
    cut('Mtot',p('bJ')*p('sixq6')*p('Hp'))
    cut('Dg',p('Dtau')*p('Df'))
    rg=p('Mtot')**2*p('Dg')
    cut('N',p('Q')*(p('Znum')**2-rg*p('V2'))+rg-p('Znum')**2)
    require(used==set(defs),'uncovered actual rows '+str(set(defs)-used))
    return receipts

def leading(g):
    env={v:(1,Poly.v(v)) for v in g['witnesses']}
    env.update({v:(0,Poly.v(v)) for v in g['fixed_numerals']})
    def get(x):return (0,Poly(x)) if type(x)==int else env[x]
    receipts=[]
    for name,op,a,b in g['source']:
        da,x=get(a);db,y=get(b)
        if op=='*':d,top=da+db,x*y
        elif da>db:d,top=da,x
        elif db>da:d,top=db,y if op=='+' else -y
        else:d,top=da,x+y if op=='+' else x-y
        require(bool(top.d),'complete leading cancellation at '+name)
        env[name]=(d,top);receipts.append({'register':name,'degree':d,'leading_terms':len(top.d)})
    q0=Poly.v('beta')*Poly.v('J');k0=Poly.v('eta')+Poly.v('zeta')
    w,s,i,T,F,alpha=(Poly.v(x) for x in ('w','s','i','T','F','alpha'))
    c0=q0-F-alpha;bb=k0*s*T-q0*q0*(q0-F)
    if g['transport_weight']=='bV':
        expected=-9*2**12*q0**128*w**34*s**78*i**14*k0**44*bb**2
    else:
        expected=9*2**16*q0**166*w**46*s**104*i**20*k0**60*bb**4*c0**2
    d,top=env[g['output']]
    require(d==g['exact_degree'],'degree header')
    require(top==expected,'full highest homogeneous polynomial')
    return {'degree':d,'highest_homogeneous_terms':top.serial(),'registers':receipts}

def coefficients(g):
    vals={};receipt=[]
    for name,item in g['coefficient_binding']['ports'].items():
        p=ROOT/g['coefficient_binding']['path']/item['file']
        blob=p.read_bytes();raw=gzip.decompress(blob)
        require(hashlib.sha256(blob).hexdigest()==item['gzip_sha256'],'coefficient compressed hash '+name)
        require(hashlib.sha256(raw).hexdigest()==item['raw_sha256'],'coefficient raw hash '+name)
        vals[name]=int.from_bytes(raw,'little')
        require(vals[name].bit_length()==item['bits'],'coefficient bits '+name)
        receipt.append({'name':name,'bits':item['bits'],'raw_sha256':item['raw_sha256']})
    require(vals['beta']>=31 and vals['beta']%2==1 and vals['K0']>0 and 0<vals['MC']<vals['beta']<vals['MF']<2*vals['beta'],'port box')
    return receipt

def algebra():
    k,t,v,C,Z=(Poly.v(x) for x in ('k','t','v','C','Z'))
    require(k*(k*k-4)-t*(t*t-4)==(k-t)*(k*k+k*t+t*t-4),'cubic difference')
    kk=t+8*v*C+32*v*v*Z
    S=kk*kk+kk*t+t*t-4
    require(192*v*v*Z-v*(kk-t)*S==8*v*v*(24*Z-(C+4*v*Z)*S),'inverse-Lucas second-order remainder')
    n=Poly.v('n0')
    require((2*n)*((2*n)**2-4)==8*n*(n*n-1),'binomial cubic identity, with 6C=n(n^2-1)')
    q,w,s=(Poly.v(x) for x in ('q','w','s'))
    require((w*q)*(q*s)**2==q**3*w*s*s,'visible q-cube factor in v')
    Q,Z,M,G,V=(Poly.v(x) for x in ('Q','Z','M','G','V'))
    require(Q*(Z*Z-M*M*G*V*V)+M*M*G-Z*Z==(Q-1)*Z*Z-M*M*G*(Q*V*V-1),'finalizer')
    J,beta,F,alpha,MC,MF=(Poly.v(x) for x in ('J','beta','F','alpha','MC','MF'))
    h=beta*J;q=h+1;C=q-F-alpha
    R=(h*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    require(R==(h*C+q*alpha)*(q*q-1)+(MC+q*MF)*J,'outer signed mask identity')
    return 6

def psi(A,n):
    x,y=0,1
    for _ in range(n):x,y=y,2*A*y-x
    return x

def finite_lucas_controls():
    count=0
    for v in range(1,19):
        for n in range(1,31):
            actual=psi(1+2*v,n)
            expected=sum((4*v)**j*math.comb(n+j,2*j+1) for j in range(n))
            require(actual==expected,'finite recurrence expansion')
            tail=(2*actual-2*n-8*v*math.comb(n+1,3))
            require(tail>=0 and tail%(32*v*v)==0,'finite second-order positive tail')
            count+=1
    corrected=0
    for q in (2,3,4,6,8,9,12,18,30,32,36):
        for w,s in ((1,1),(2,3)):
            v=q**3*w*s*s
            for n in range(1,17):
                k=2*psi(1+2*v,n)
                require(v*k*(k*k-4)%6==0,'inverse correction integral')
                for r in range(1,17):
                    eb=k-2*r-v*k*(k*k-4)//6;d=2*(n-r)
                    require(3*(eb-d)%(4*v*v)==0,'finite exact remainder divisibility')
                    require((eb-d)%q**4==0,'finite all-prime q4 congruence')
                    if d==0 and q&(q-1)==0:require(eb%q**6==0,'finite dyadic full denominator')
                    corrected+=1
    q=3;v=27;n=2;k=2*psi(1+2*v,n)
    counterexample=k-2*n-v*k*(k*k-4)//6
    require(counterexample%q**6==243,'missing third-primary denominator counterexample')
    return {'recurrence_cases':count,'corrected_index_cases':corrected,
            'premature_q6_counterexample':{'q':q,'v':v,'n0':n,'e':counterexample,'remainder_mod_q6':243},
            'scope':'finite diagnostic controls only; not a universal number-theoretic proof'}

def mutations(g):
    rejected=0
    for idx,row in enumerate(g['source']):
        for op in ('+','-','*'):
            if op==row[1]:continue
            bad=copy.deepcopy(g);bad['source'][idx][1]=op
            try:exact_cuts(bad)
            except (ValueError,KeyError):rejected+=1
            else:raise ValueError('undetected operator corruption '+str(idx)+' '+op)
    bad=copy.deepcopy(g)
    for row in bad['source']:
        if row[0]=='eclear':row[3]='six_e_sigma'
    try:exact_cuts(bad)
    except (ValueError,KeyError):rejected+=1
    else:raise ValueError('undetected missing correction')
    return rejected

def check_source_pins():
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for rel,digest in pins['files'].items():
        require(hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==digest,'source pin '+rel)
    return len(pins['files'])

def reconstruct_coefficients():
    spec=importlib.util.spec_from_file_location('independent_literal_coefficient_recipe',ROOT/'inherited_lucas'/'parent'/'rebuild_coefficients.py')
    recipe=importlib.util.module_from_spec(spec);spec.loader.exec_module(recipe)
    return recipe.check_or_write(False)

def main():
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);args=ap.parse_args()
    result={'source_pins':check_source_pins(),'coefficient_reconstruction':reconstruct_coefficients(),'algebraic_identities':algebra(),'finite_controls':finite_lucas_controls(),'circuits':[],
            'interpretation':'Exact finite artifact checks plus separately labelled finite recurrence controls. The unbounded arithmetic proof is PROOF.md, with inherited calibration explicitly retained.'}
    for weight in ('V2','bV'):
        path=ROOT/f'equation_{weight}.json';g=json.loads(path.read_text())
        result['circuits'].append({'file':path.name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'operations':g['operations'],'operation_breakdown':topology(g),
            'exact_cuts':exact_cuts(g),'leading':leading(g),'coefficients':coefficients(g),
            'rejected_actual_mutations':mutations(g)})
    side_spec=importlib.util.spec_from_file_location('whole47_specialization_checker',ROOT/'radix47'/'verify.py')
    side=importlib.util.module_from_spec(side_spec);side_spec.loader.exec_module(side)
    result['whole47']=side.run()
    if args.receipt:args.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'source_pins':result['source_pins'],'whole47':{'raw_bytes':result['whole47']['raw_bytes'],'largest_port_bits':result['whole47']['largest_port_bits']},'identities':result['algebraic_identities'],'finite_controls':result['finite_controls'],
        'circuits':[{'file':r['file'],'operations':r['operations'],'degree':r['leading']['degree'],
                     'cuts':len(r['exact_cuts']),'leading_terms':len(r['leading']['highest_homogeneous_terms']),
                     'rejected_mutations':r['rejected_actual_mutations']} for r in result['circuits']]},indent=2))

if __name__=='__main__':main()
