#!/usr/bin/env python3
"""Independent exact checks for the two-root carriers; no producer import.

Algebraic and finite-data verification only. The unbounded proof is PROOF.md.
"""
from pathlib import Path
from collections import Counter
import copy,hashlib,json,math,subprocess,sys

HERE=Path(__file__).resolve().parent

def need(test,message):
    if not test:raise ValueError(message)

class Poly:
    def __init__(self,x=0):self.t=dict(x) if isinstance(x,dict) else {():x} if x else {}
    @staticmethod
    def sym(s):return Poly({(s,):1})
    @staticmethod
    def lift(x):return x if isinstance(x,Poly) else Poly(x)
    def __add__(self,b):
        b=self.lift(b);r=dict(self.t)
        for m,c in b.t.items():
            r[m]=r.get(m,0)+c
            if not r[m]:del r[m]
        return Poly(r)
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.t.items()})
    def __sub__(self,b):return self+-self.lift(b)
    def __rsub__(self,b):return self.lift(b)+-self
    def __mul__(self,b):
        b=self.lift(b);r={}
        for m,c in self.t.items():
            for n,d in b.t.items():
                k=tuple(sorted(m+n));r[k]=r.get(k,0)+c*d
        return Poly({m:c for m,c in r.items() if c})
    __rmul__=__mul__
    def __pow__(self,n):
        r=Poly(1);b=self
        while n:
            if n&1:r=r*b
            n//=2
            if n:b=b*b
        return r
    def __eq__(self,b):return self.t==self.lift(b).t

def univar_add(a,b,sign=1,mod=None):
    r=[0]*max(len(a),len(b))
    for i,c in enumerate(a):r[i]+=c
    for i,c in enumerate(b):r[i]+=sign*c
    if mod:r=[c%mod for c in r]
    while len(r)>1 and not r[-1]:r.pop()
    return r

def univar_mul(a,b,mod=None):
    r=[0]*(len(a)+len(b)-1)
    for i,c in enumerate(a):
        for j,d in enumerate(b):r[i+j]+=c*d
    if mod:r=[c%mod for c in r]
    while len(r)>1 and not r[-1]:r.pop()
    return r

def topology(g):
    known=set(g['witnesses']+g['fixed_numerals']);rows={}
    for name,op,l,r in g['source']:
        need(name not in known,'Duplicate name')
        need(op in ('+','-','*'),'Invalid operation')
        need(all(type(x) is int or x in known for x in (l,r)),'Forward reference')
        known.add(name);rows[name]=(l,r)
    live=set();stack=[g['output']]
    while stack:
        x=stack.pop()
        if type(x) is int or x in live:continue
        live.add(x);stack.extend(rows.get(x,()))
    need(known==live,'Dead gate, input, or coefficient')
    need(g['operations']==len(rows),'Operation metadata')
    need(g['operation_counts']==dict(sorted(Counter(r[1] for r in g['source']).items())),'Operation split')

def formal_cuts(g,mode):
    names=set(g['witnesses']+g['fixed_numerals']+[r[0] for r in g['source']])
    s={n:Poly.sym(n) for n in names}
    e={
      'qm':s['beta']*s['J'], 'q':s['qm']+1,
      'X':s['w']*s['q'], 'Y':s['s']*s['q']**3,
      'E':s['X']*s['Y'], 'k':s['eta']+s['zeta'],
      'ell':s['E']*s['k']*s['Y'], 'c':s['k']*s['Y']+s['eta'],
      'a':s['E']+s['Y'], 'H':4*s['a']+3,
      'Delta':s['a']**2+s['H'],
      'main_root':s['X']+s['a']*s['c']+s['gamma']*s['H'],
      'N1':s['main_root']**2-s['Delta']*s['c']**2,
      'C':s['q']-s['F']-s['alpha'],
      'R':(s['qm']*(s['q']-s['F'])+s['alpha'])*(s['q']**2-1)+(s['MC']+s['q']*s['MF'])*s['J'],
      'tau':s['E']*s['n']+s['k']-s['R'],
      'N0':s['tau']**2-s['ell']*(s['ell']+s['k']),
      'B':(s['K0']+s['w'])*s['C']-s['F'],
      'cTminusR':s['c']*s['T']-s['R'],
      'V':s['f']**2*s['cTminusR']-s['c'],
      'normalized_S':s['qm']*s['i']*s['Delta']*s['c']**2,
      'Na':s['normalized_S']**2*(s['V']**2-s['y']**2)+s['y']**2,
      'scaled_Ns':s['Delta']*s['f']**2-s['normalized_S']**2,
      'polynomial':s['N0']*s['N1']*s['Na']*s['scaled_Ns']-s['Delta'],
    }
    if mode=='oriented':
        e['L']=s['cTminusR']*s['V'];L=s['L']
    else:L=s['V']**2
    e['y']=1+4*(s['qm']*(s['m']-L*s['B'])-s['B'])
    env={n:s[n] for n in g['witnesses']+g['fixed_numerals']};checked=[]
    for name,op,l,r in g['source']:
        a=Poly(l) if type(l) is int else env[l]
        b=Poly(r) if type(r) is int else env[r]
        v=a+b if op=='+' else a-b if op=='-' else a*b
        if name in e:
            need(v==e[name],'Formal formula mismatch '+name)
            checked.append(name);env[name]=s[name]
        else:env[name]=v
    need(set(checked)==set(e),'Missed formal cut')
    return len(checked)

def coefficient_check():
    meta=json.loads((HERE/'coefficients.json').read_text())
    values={};record={}
    for k,filename in [('beta','beta.bin'),('K0','K.bin'),('MC','MC.bin'),('MF','MF_source.bin')]:
        raw=(HERE/'coefficients'/filename).read_bytes()
        # Parent manifest uses K0 or K depending on its original printing.
        mk=k if k in meta else 'K' if k=='K0' else 'MF_source' if k=='MF' else k
        m=meta[mk]
        need(len(raw)==m['bytes'],'Coefficient byte length')
        need(hashlib.sha256(raw).hexdigest()==m['sha256'],'Coefficient hash')
        need(raw and raw[0]!=0,'Nonminimal coefficient encoding')
        values[k]=int.from_bytes(raw,'big')
        record[k]={'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
    need(values['beta']>=31 and values['K0']>0 and 0<values['MC']<values['beta']<values['MF']<2*values['beta'],'Scalar tuple bounds')
    return values,record

def degree(g,mode,values):
    # Upper bounds from the formal cuts and the exact N1 cancellation.
    d={n:1 for n in g['witnesses']};d.update({n:0 for n in g['fixed_numerals']})
    for name,op,l,r in g['source']:
        a=0 if type(l) is int else d[l];b=0 if type(r) is int else d[r]
        d[name]=a+b if op=='*' else max(a,b)
        if name=='N1':d[name]=18
    expected=174 if mode=='square' else 170
    need(d[g['output']]==expected,'Incorrect global degree upper bound')
    modulus=1000000007
    primes=[2,3,5,7,11,13,17,19,23,29,31,37,41]
    scalar=dict(zip(g['witnesses'],primes))
    env={n:[0,v] for n,v in scalar.items()};env.update({n:[v%modulus] for n,v in values.items()})
    for name,op,l,r in g['source']:
        a=[l%modulus] if type(l) is int else env[l]
        b=[r%modulus] if type(r) is int else env[r]
        env[name]=univar_mul(a,b,modulus) if op=='*' else univar_add(a,b,1 if op=='+' else -1,modulus)
    need(len(env[g['output']])-1==expected,'Fixed-tuple exact degree lower bound failed')
    q0=values['beta']%modulus*scalar['J']%modulus;k0=scalar['eta']+scalar['zeta']
    leading=-128*pow(q0,99,modulus)*scalar['gamma']*scalar['i']**4*k0**15*scalar['w']**14*scalar['s']**27*scalar['f']**(8 if mode=='square' else 4)*scalar['T']**4*(q0-scalar['F']-scalar['alpha'])**2
    need(env[g['output']][-1]==leading%modulus!=0,'Expected leading form specialization')
    return {'exact_degree':expected,'factor_degrees':{n:d[n] for n in ['N0','N1','Na','scaled_Ns']},'fixed_tuple_specialization_modulus':modulus,'nonzero_top_coefficient_modulus':env[g['output']][-1]}

def full_leader(g,mode):
    # Exact homogeneous polynomial propagation, with the sole N1 cancellation
    # replaced by its verified, exact degree-18 homogeneous component.
    s={n:Poly.sym(n) for n in g['witnesses']+g['fixed_numerals']}
    d={n:1 for n in g['witnesses']};d.update({n:0 for n in g['fixed_numerals']})
    env=dict(s)
    q0=s['beta']*s['J'];k0=s['eta']+s['zeta']
    for name,op,l,r in g['source']:
        a=Poly(l) if type(l) is int else env[l]
        b=Poly(r) if type(r) is int else env[r]
        da=0 if type(l) is int else d[l];db=0 if type(r) is int else d[r]
        if name=='N1':
            env[name]=8*s['gamma']*k0*s['w']**2*s['s']**3*q0**11;d[name]=18
        elif op=='*':env[name]=a*b;d[name]=da+db
        else:
            high=max(da,db)
            env[name]=(a if da==high else Poly())+(b if db==high else Poly())*(1 if op=='+' else -1)
            d[name]=high;need(env[name].t,'Unexpected leading cancellation at '+name)
    leader=-128*q0**99*s['gamma']*s['i']**4*k0**15*s['w']**14*s['s']**27*s['f']**(8 if mode=='square' else 4)*s['T']**4*(q0-s['F']-s['alpha'])**2
    need(env[g['output']]==leader,'Whole highest homogeneous polynomial')
    return len(leader.t)

def main_norm_identity():
    a,c,X,gamma,H=[Poly.sym(n) for n in ['a','c','X','gamma','H']]
    Z=X+gamma*H
    need((a*c+Z)**2-(a*a+H)*c*c==2*a*c*Z+Z*Z-H*c*c,'Exact main-norm degree cancellation')

def corruption_controls(g,mode):
    controls=[]
    for target,index,value in [('four_carrier',2,2),('hi',2,1),('carrier',1,'+'),('product4',2,1),('B',1,'+')]:
        bad=copy.deepcopy(g)
        next(r for r in bad['source'] if r[0]==target)[index]=value
        bad['operation_counts']=dict(sorted(Counter(r[1] for r in bad['source']).items()))
        try:formal_cuts(bad,mode)
        except ValueError:controls.append(target)
        else:raise ValueError('Altered graph escaped formal checks: '+target)
    return controls

def fixtures():
    count=0
    for h in range(1,9):
        for S in range(max(2,h),9*h+1,h):
            x,u=1,0
            for r in range(1,12):
                x,u=S*x+(S*S-1)*u,x+S*u
                if r%2==0:continue
                need((u-(-1)**((r-1)//2))%(4*S*S)==0,'Odd-ordinate congruence')
                V=x//S;need(x%S==0,'Odd abscissa divisibility')
                y=u if u%4==1 else -u
                for multiplier in range(1,4):
                    B=h*multiplier;L=V*V
                    need((y-1)%(4*h)==0,'Completeness numerator integrality')
                    m=(y-1)//(4*h)+(1+h*L)*(B//h)
                    need(m>0,'Completeness carrier positivity')
                    need(y==1+4*(h*(m-L*B)-B),'Carrier reconstruction')
                    need(S*S*V*V-(S*S-1)*y*y==1,'Auxiliary norm')
                    count+=1
    return count

def integer_lift(z,g):
    topology(z)
    need(len(z['witnesses'])==39 and z['witness_domain']=='unrestricted integers','Integer domain')
    n=7*13
    need(z['source'][n:]==g['source'],'Integer lift changed original expression')
    need(z['exact_degree']==2*g['exact_degree'],'Integer degree')
    for j,name in enumerate(g['witnesses']):
        aa,bb,cc=name+'_a',name+'_b',name+'_c'
        rows=z['source'][7*j:7*j+7]
        env={aa:Poly.sym(aa),bb:Poly.sym(bb),cc:Poly.sym(cc)}
        for v,op,l,r in rows:
            a=Poly(l) if type(l) is int else env[l];b=Poly(r) if type(r) is int else env[r]
            env[v]=a+b if op=='+' else a-b if op=='-' else a*b
        need(env[name]==1+env[aa]**2+env[bb]**2+env[cc]*(env[cc]+1),'Positive parametrization')
    return {'variables':39,'operations':z['operations'],'degree':z['exact_degree'],'exact_degree_reason':'Set each second and third coordinate to zero in the highest form; monomial doubling is injective.'}

def main():
    values,coeffs=coefficient_check();reports=[]
    main_norm_identity()
    reconstruction=json.loads(subprocess.check_output([sys.executable,'-B',str(HERE/'reconstruct_coefficients.py')],text=True))
    source_ledger=json.loads((HERE/'SOURCES.json').read_text())
    for item in source_ledger['frozen_files']:
        need(hashlib.sha256((HERE/item['local']).read_bytes()).hexdigest()==item['sha256'],'Frozen source bytes '+item['local'])
    original=json.loads((HERE/'parent65.json').read_text())
    for mode in ['square','oriented']:
        path=HERE/('positive13_'+mode+'.json');g=json.loads(path.read_text())
        need(g['witnesses']==['J','F','alpha','f','i','T','s','w','n','eta','zeta','m','gamma'],'Positive input list')
        need(g['witness_domain']=='strictly positive integers','Positive domain')
        need(g['parent_sha256']==hashlib.sha256((HERE/'parent65.json').read_bytes()).hexdigest(),'Parent binding')
        need(g['fixed_numerals']==original['fixed_numerals'] and g['coefficient_binding']==original['coefficient_binding'],'Whole tuple binding')
        topology(g);cuts=formal_cuts(g,mode);deg=degree(g,mode,values);terms=full_leader(g,mode);controls=corruption_controls(g,mode)
        z=json.loads((HERE/('integer39_'+mode+'.json')).read_text());lift=integer_lift(z,g)
        reports.append({'mode':mode,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'variables':13,'operations':g['operations'],'operation_counts':g['operation_counts'],'formal_cuts':cuts,'leading_form_terms':terms,**deg,'integer_lift':lift,'corruption_controls':controls})
    result={'status':'PASS','scope':'Exact finite algebra, coefficients, domains, and fixtures; no unbounded or logical theorem is proved by testing.','equations':reports,'coefficients':coeffs,'pell_carrier_fixtures':fixtures(),'coefficient_reconstruction':reconstruction,'frozen_source_files':len(source_ledger['frozen_files'])}
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
