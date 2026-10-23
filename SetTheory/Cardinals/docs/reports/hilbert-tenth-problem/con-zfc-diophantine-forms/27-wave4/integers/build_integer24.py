#!/usr/bin/env python3
"""Literal 24-integer norm circuits. Exact binary +,-,* ledgers; no external packages.
Source arithmetic adapted from ProveIt package21 at the pin in PROVENANCE.json.
Finite identity checks are not a proof of compiler semantics or ZFC consistency.
"""
from pathlib import Path
from copy import deepcopy
from collections import Counter
import importlib.util, json, random, hashlib
HERE=Path(__file__).resolve().parent
SRC=HERE/'sources/21-norm12/arithmetic/build_norm12.py'
spec=importlib.util.spec_from_file_location('source_norm',SRC);base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
GUARDED=['J','F','alpha','z','eta','zeta']
FREE=['ii','ss','ww','h','T','r']
PIN='ae3007ca4467011e0e051c84acb4a1dd13971b0e'
ROOT='https://github.com/VladimirReshetnikov/ProveIt/blob/'+PIN+'/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/'
BIND=json.loads((HERE/'COEFFICIENT_BINDING.json').read_text())

def ledger(p):
    names=set(p['witnesses']+p['fixed_numerals']);degree={n:1 for n in p['witnesses']};degree.update({n:0 for n in p['fixed_numerals']})
    for n,op,a,b in p['source']:
        assert n not in names and op in ('+','-','*')
        assert all(isinstance(x,int) or x in names for x in [a,b]);names.add(n)
        da=0 if isinstance(a,int) else degree[a];db=0 if isinstance(b,int) else degree[b];degree[n]=da+db if op=='*' else max(da,db)
    out=[p['output']] if 'output' in p else [x for pair in p['comparisons'] for x in pair if isinstance(x,str)]
    live=set(out)
    for n,_,a,b in reversed(p['source']):
        if n in live:live.update(x for x in (a,b) if isinstance(x,str))
    assert all(n in live for n,_,_,_ in p['source']);assert set(p['witnesses']+p['fixed_numerals'])<=live
    ct=Counter(row[1] for row in p['source']);p['ledger']={'operations':len(p['source']),'multiplications':ct['*'],'additions_subtractions':ct['+']+ct['-'],'all_gates_live':True,'all_ports_live':True,'syntactic_degree_upper_bounds':{n:degree[n] for n in out}}
    return degree

def lift(p):
    p=deepcopy(p);prefix=[];witnesses=[]
    for n in GUARDED:
        x,y,t=[n+'_'+v for v in ['x','y','t']];witnesses += [x,y,t]
        prefix += [[n+'_x2','*',x,x],[n+'_y2','*',y,y],[n+'_tp1','+',t,1],[n+'_pronic','*',t,n+'_tp1'],[n+'_sum0','+',n+'_x2',n+'_y2'],[n+'_sum1','+',n+'_sum0',n+'_pronic'],[n,'+',n+'_sum1',1]]
    witnesses+=FREE
    prefix += [['twice_ii','*',2,'ii'],['i','+','twice_ii',1],['twice_ss','*',2,'ss'],['s','+','twice_ss',1],['w','*','ww','ww']]
    assert len(witnesses)==24 and len(prefix)==47
    p.update(source=prefix+p['source'],witnesses=witnesses,domain='unrestricted integers',coefficient_binding=BIND)
    return p

def packets(split):
    ps=base.construct()
    for p in ps:
        if split:
            src=[]
            for row in p['source']:
                if row[0]=='HL2':src += [['HM','*',2,'HBnd'],['HL2','*','HM','HM']]
                else:src.append(row)
            p['source']=src
        p=lift(p)
        tag='split2' if split else 'original'
        form=p['name'].split('_')[-1]
        p['name']='integer24_'+tag+'_'+form
        if form=='system':p['residual_exact_degrees']=[12,4,2240 if split else 2416]
        else:p['exact_degree']=(2256 if split else 2432) if form=='product' else (4480 if split else 4832)
        ledger(p)
        yield p
        if form=='system':
            q=deepcopy(p);q['name']+='_comparison';q['source']=[r for r in q['source'] if r[0]!='N'];q['comparisons']=[['Nk',1],['Nt',1],['N00','GN11']]
            ledger(q);yield q
            q=deepcopy(p);q['name']+='_residual';q['source'] += [['rk','-','Nk',1],['rt','-','Nt',1]];q['comparisons']=[['rk',0],['rt',0],['N',0]]
            ledger(q);yield q

def ratio_packets():
    for p in packets(True):
        p=deepcopy(p);p['name']=p['name'].replace('split2','ratio')
        src=[]
        for row in p['source']:
            if row[0] in ['bound0','bound1']:continue
            if row[0]=='Bnd':
                src += [['iI','*','i','I'],['Rac','*','R','ac'],['fiveRac','*',5,'Rac'],['ratioFactor','+','fiveRac',1],['ratioProd','*','iI','ratioFactor'],['ratioSum','+','ratioProd','v2'],['Bnd','*',2,'ratioSum']]
            else:src.append(row)
        p['source']=src
        p['weight_definition']='Bnd denotes W=2*((i*I)*(1+5*R*ac)+v^2), not the original primary bound.'
        if 'output' in p:p['exact_degree']=1936 if p['output']=='polynomial' else 3840
        else:p['residual_exact_degrees']=[12,4,1920]
        ledger(p);yield p

def back(vals):
    v={n:vals[n+'_x']**2+vals[n+'_y']**2+vals[n+'_t']*(vals[n+'_t']+1)+1 for n in GUARDED}
    v.update(i=2*vals['ii']+1,s=2*vals['ss']+1,w=vals['ww']**2,h=vals['h'],T=vals['T'],r=vals['r']);v.update({n:vals[n] for n in base.FIXED});return v

def independent_norm(a,split):
    G,A,D=a['G'],a['A'],a['D']
    def product(x,y):
        z=[0]*8
        for j,v in enumerate(x):
            for k,w in enumerate(y):
                factor=(G if j&k&1 else 1)*(A if j&k&2 else 1)*(D if j&k&4 else 1)
                z[j^k]+=factor*v*w
        return z
    B=2*a['Q']*a['v']*a['b'];acc=[1]+[0]*7
    ht=2*a['H']*a['Bnd'] if split else a['H']*a['L']
    for su in [-1,1]:
      for st in [-1,1]:
       for sf in [-1,1]:
        root=[a['S'],-su*a['L'],-st*ht,0,0,0,0,0]
        w=[a['d']*x for x in product(root,root)];w[0]-=a['H']**2*a['e'];w[4]+=sf*a['H']**2*B;acc=product(acc,w)
    assert not any(acc[1:]);return acc[0]

def leading(p,prime,seed):
    rng=random.Random(seed)
    val={n:(1,rng.randrange(1,prime)) for n in p['witnesses']};val.update({n:(0,c) for n,c in zip(base.FIXED,[31,127,10,45])})
    for n,op,l,r in p['source']:
        dl,cl=(0,l%prime) if isinstance(l,int) else val[l];dr,cr=(0,r%prime) if isinstance(r,int) else val[r]
        if op=='*':val[n]=(dl+dr,cl*cr%prime)
        else:
            degree=max(dl,dr);coef=((cl if dl==degree else 0)+(cr if dr==degree else 0)*(1 if op=='+' else -1))%prime
            val[n]=(degree,coef)
    # Leading-only arithmetic is deliberately not an exact degree algorithm when cancellation occurs.
    # The structural norm leader is checked directly as a polynomial identity at sampled leading forms.
    return val

def bounds_checks():
    from fractions import Fraction
    count=0
    for q in [16,17,31]:
      for sw in [0,1,4]:
       for s in [-7,-3,-1,1,3,7]:
        for eta,zeta in [(1,1),(2,3),(11,1)]:
         for i in [-3,-1,1,3]:
          for T in [-3,0,2]:
           for R in [q*(q*q-1)+1,q**4-3]:
            X=sw*q;Y=s*q**3;k=eta+zeta;c=k*Y+eta;a=(X+1)*Y;H=4*a+3;delta=a*a+H
            D=1+delta*i*i*c**4;Q=(delta*i*c*c)**2;b=c+R*D;v=c*T;Bnd=v*v+D+2*b;B=abs(H)*Bnd;L=1+H*Bnd;G=1+delta*c*c;ell=X*k*Y*Y;A=1+ell*(ell+k)
            assert abs(H)>6 and G>4 and delta>R and D>delta+abs(c) and 1<b<Q and 2*abs(L)>B
            assert L*L*G>B*B
            if X:
                assert 4*G<9*A and A>16 and B>8 and 8*abs(L)<9*B
                assert 16*G<256*A # coarse original bound
            count+=1
    return count

def main():
    allps=list(packets(False))+list(packets(True))+list(ratio_packets());receipt=[];rng=random.Random(241023);checks={}
    for mode in ['original','split2','ratio']:
        split=mode!='original'
        systems=[p for p in allps if p['name']=='integer24_'+mode+'_system'];p=systems[0]
        for _ in range(48):
            v={n:rng.randrange(-2,3) for n in p['witnesses']};v.update(zip(base.FIXED,[15,127,10,45]));a=base.evaluate(p,v)
            assert a['N']==independent_norm(a,split)
            assert a['N1']%8==0 and (a['N']-a['N0']**2)%64==0
            if not split:assert a['N']==base.evaluate(base.construct()[0],back(v))['N']
        checks[mode+'_direct_conjugate_fixtures']=48
    for p in allps:
        p['source_sha256']=hashlib.sha256(json.dumps(p['source'],separators=(',',':')).encode()).hexdigest()
        (HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
        receipt.append({k:p[k] for k in ['name','ledger','exact_degree','residual_exact_degrees'] if k in p})
    checks['leading_form_diagnostics']=[]
    for mode in ['original','split2','ratio']:
        split=mode!='original'
        p=next(p for p in allps if p['name']=='integer24_'+mode+'_product')
        for prime,seed in [(1000000007,241),(1000000009,242)]:
            lead=leading(p,prime,seed)
            top=lambda n:lead[n][1]
            expected=(pow(3,8,prime)*pow(top('d'),8,prime)*pow(top('H')*top('Bnd')*top('ell'),16,prime))%prime if split else (pow(top('d'),8,prime)*pow(top('H'),16,prime)*pow(top('L'),16,prime)*pow(top('A'),8,prime))%prime
            if mode=='ratio': expected=pow(99*899,4,prime)*pow(top('d'),8,prime)*pow(top('H'),16,prime)*pow(top('b'),16,prime)%prime
            assert lead['N'][0]==({'original':2416,'split2':2240,'ratio':1920}[mode]) and lead['N'][1]==expected and expected!=0
            assert lead['polynomial'][0]==p['exact_degree'] and lead['polynomial'][1]!=0
            checks['leading_form_diagnostics'].append({'packet':p['name'],'prime':prime,'seed':seed,'norm':lead['N'],'product':lead['polynomial'],'structural_norm_leader_matches':True})
    checks['signed_boundary_bound_fixtures']=bounds_checks()
    checks['scope']='Finite exact algebra/bound fixtures supplement the proofs; no accepting machine witness or formal semantic proof.'
    (HERE/'INTEGER24_CHECKS.json').write_text(json.dumps({'packets':receipt,'checks':checks},indent=2)+'\n')
    print(json.dumps({'packets':receipt,'checks':checks},indent=2))
if __name__=='__main__':main()
