#!/usr/bin/env python3
"""Read-only finite verification of the positive quotient-chart equations.

Standard library only. No file is written unless --output is supplied.
The checks establish the literal circuits, identities, coefficient bytes and
degree controls. The unbounded arithmetic proof is in PROOF.md.
"""
import sys
sys.dont_write_bytecode = True

import argparse
from collections import Counter, defaultdict
from functools import lru_cache
import gzip
import hashlib
import importlib.util
import json
import random
from pathlib import Path

HERE = Path(__file__).resolve().parent
NAMES = ('quotient', 'quotient_absorbed', 'quotient_sharp', 'quotient_absorbed_sharp')
WITNESSES = ['J','F','alpha','i','T','w','s','n','eta','zeta']
PORTS = ['beta','K0','MC','MF']
PRIMES = ((1 << 61)-1, (1 << 89)-1)
PINNED_RAW = {
    'beta':'0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d',
    'K0':'c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e',
    'MC':'6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4',
    'MF':'48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737'}
TRANSITION_SHA = '4daefec3566fe595102a5fe7de9f7fa5d39d4b5f039a0cee260f62b83c43a4ee'


class Failure(ValueError):
    pass


def require(ok, message):
    if not ok:
        raise Failure(message)


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


# A small, independently implemented free integer polynomial ring.
def const(n):
    return {(): n} if n else {}


def symbol(name):
    return {(name,): 1}


def add(*ps):
    out = defaultdict(int)
    for p in ps:
        for m,c in p.items():
            out[m] += c
    return {m:c for m,c in out.items() if c}


def scale(p, n):
    return {m:n*c for m,c in p.items() if n*c}


def sub(p,q):
    return add(p,scale(q,-1))


def mul(p,q):
    out = defaultdict(int)
    for a,c in p.items():
        for b,d in q.items():
            out[tuple(sorted(a+b))] += c*d
    return {m:c for m,c in out.items() if c}


def power(p,n):
    out = const(1)
    for _ in range(n):
        out = mul(out,p)
    return out


def expand(equation, target, cuts):
    rows = {r[0]:r for r in equation['source']}
    @lru_cache(None)
    def go(name):
        if isinstance(name,int):
            return const(name)
        if name in cuts:
            return cuts[name]
        require(name in rows,'unbound symbolic cut: '+name)
        _,op,a,b = rows[name]
        return {'+':add,'-':sub,'*':mul}[op](go(a),go(b))
    return go(target)


def norm(z,m,d,a,num):
    u = mul(d,mul(power(m,2),a))
    v = mul(power(m,2),num)
    return sub(power(sub(sub(mul(d,power(z,2)),v),u),2),scale(mul(u,v),4))


def symbolic_checks(e,parent):
    absorbed = '_absorbed' in e['name']
    sharp = e['name'].endswith('_sharp')
    old = {r[0]:r for r in parent['source']}
    new = {r[0]:r for r in e['source']}
    require(set(old)-set(new)=={'P1','lowY','q3WBt','inner'},'unexpected deleted registers')
    require(set(new)-set(old)==({'Y'} if absorbed else {'Y','ns'}),'unexpected new registers')
    permitted = {'P1mu2','mu2inner','P1e','brk','Znum'} | (set() if absorbed else {'nV'})
    for node in set(old)&set(new)-permitted:
        require(old[node]==new[node],'unlicensed kernel/finalizer edit: '+node)
    require(new['Y']==['Y','*','q3','s'],'wrong quotient chart')
    require(new['q3']==['q3','*','q2','q'],'q3 is not the literal cube gate')
    q3,g,u,h,n,v,gamma,b,bt,k,ee,ss = map(symbol,
        ('q3','g','U','H','n','V','Gamma','b','B','K','e','s'))
    center = gamma if sharp else const(0)
    cuts = {'q3':q3,'bJ':g,'mu2':u,'Hp':h,'n':n,'V':v,'Cg':center,
            'cTR':b,'B':bt,'Kpos':k,'e':ee,'s':ss}
    padding = n if absorbed else add(n,ss)
    expected_z = sub(mul(mul(g,u),add(mul(h,sub(add(padding,v,center),mul(b,bt))),k)),
                     mul(h,add(mul(u,bt),mul(g,ee))))
    zn = expand(e,'Znum',cuts)
    mn = expand(e,'Mtot',cuts)
    require(zn==expected_z,'new carrier differs from independently stated formula')
    require(mn==mul(g,mul(u,h)),'new primitive denominator is wrong')
    oldcuts = dict(cuts)
    oldcuts['Y'] = mul(q3,ss)
    oldcuts['n'] = sub(n,ss) if absorbed else n
    require(expand(parent,'Znum',oldcuts)==mul(q3,zn),'exact old/new carrier identity failed')
    require(expand(parent,'Mtot',oldcuts)==mul(q3,mn),'exact old/new denominator identity failed')
    z,m,d,a,num = map(symbol,('z','m','delta','a','num'))
    nf = norm(z,m,d,a,num)
    require(expand(e,'N',{'Znum':z,'Mtot':m,'delta':d,'pair':a,'Dnum':num})==nf,
            'finalizer differs from independent four-factor norm formula')
    require(norm(mul(q3,z),mul(q3,m),d,a,num)==mul(power(q3,4),nf),
            'norm homogeneity identity failed')
    return {'exact_cut_identities':6,'unchanged_rows':len(set(old)&set(new)-permitted)}


def universal_degree_identities():
    d,m,v,c,z0,a = map(symbol,('delta','M','V','Gamma','Z0','a'))
    zz = add(mul(m,add(v,c)),z0)
    num = sub(mul(add(d,const(1)),power(v,2)),const(1))
    defect = sub(power(c,2),a)
    theta = add(mul(d,mul(power(m,2),defect)),
                scale(mul(power(m,2),sub(power(v,2),const(1))),-1),
                scale(mul(d,mul(m,mul(add(v,c),z0))),2),mul(d,power(z0,2)))
    rhs = add(scale(mul(power(d,2),mul(power(m,4),mul(power(v,2),defect))),4),
              scale(mul(d,mul(power(m,2),mul(v,mul(c,theta)))),4),power(theta,2),
              scale(mul(d,mul(power(m,4),mul(a,power(v,2)))),-4),
              scale(mul(d,mul(power(m,4),a)),4))
    require(norm(zz,m,d,a,num)==rhs,'centered finalizer identity failed')
    aa,dd,ee = map(symbol,('A','D','E'))
    fs = add(const(1),mul(sub(power(aa,2),const(1)),mul(dd,power(ee,2))))
    require(sub(power(mul(aa,mul(dd,ee)),2),mul(dd,fs)) == sub(mul(power(dd,2),power(ee,2)),dd),
            'sharp center defect identity failed')
    # These are the degree bounds of the exact centered identity in PROOF.md.
    require(2*84+4*13+2*74+98==466,'uncentered top-degree arithmetic')
    require(2*84+4*13+2*74+82==450,'sharp top-degree arithmetic')
    require(max(2*208,84+4*13+98+2*74,84+4*13+98)<466,'uncentered competing-degree bound')
    require(max(84+2*13+74+49+192,2*192,84+4*13+98+2*74,84+4*13+98)<450,
            'sharp competing-degree bound')
    require(sum((326,10,30,64,34,2))==466 and sum((314,10,28,62,34,2))==450,
            'leading monomial degree arithmetic')
    return {'centered_identity_terms':len(rhs),'sharp_defect_terms':2,
            'degree_bounds':{'uncentered':[466,416,382,234],'sharp':[450,425,384,382,234]}}


def validate_graph(e):
    require(e['domain']=='strictly positive integers','wrong quantified domain')
    require(e['witnesses']==WITNESSES and e['fixed_numerals']==PORTS,'wrong inputs or ports')
    require(e['output']=='N','wrong output')
    known=set(WITNESSES+PORTS)
    support={x:({x} if x in WITNESSES else set()) for x in known}
    degree={x:(1 if x in WITNESSES else 0) for x in known}
    outputs=set()
    for row in e['source']:
        require(len(row)==4,'invalid row length')
        node,op,x,y=row
        require(isinstance(node,str) and node not in known,'redefined register')
        require(op in ('+','-','*'),'invalid arithmetic operator')
        require(all(isinstance(v,int) or isinstance(v,str) and v in known for v in (x,y)),
                'forward or unknown operand')
        sx=support[x] if isinstance(x,str) else set()
        sy=support[y] if isinstance(y,str) else set()
        support[node]=sx|sy
        require(bool(support[node]),'constant-only paid arithmetic row')
        dx=degree[x] if isinstance(x,str) else 0
        dy=degree[y] if isinstance(y,str) else 0
        degree[node]=dx+dy if op=='*' else max(dx,dy)
        known.add(node);outputs.add(node)
    need={'N'}
    for node,op,x,y in reversed(e['source']):
        if node in need:
            need.update(v for v in (x,y) if isinstance(v,str))
    require(outputs<=need,'dead paid arithmetic row')
    require(set(WITNESSES+PORTS)<=need,'unused quantified input or fixed port')
    split=dict(Counter(row[1] for row in e['source']))
    require(len(e['source'])==e['operations'],'operation-count mismatch')
    require(split==e['operation_breakdown'],'operation split mismatch')
    require(degree['N']==e['syntactic_degree']==516,'syntactic degree mismatch')
    sharp=e['name'].endswith('_sharp');absorbed='_absorbed' in e['name']
    require(e['exact_degree']==(450 if sharp else 466),'wrong exact-degree metadata')
    require(e['operations']==86+(3 if sharp else 0)+(0 if absorbed else 1),'wrong expected operation count')
    return {'operations':len(e['source']),'split':split,'syntactic_degree':degree['N'],
            'all_rows_live':True,'all_witnesses_and_ports_live':True}


def coefficients():
    binding=json.loads((HERE/'coefficients/BINDING.json').read_text())
    parent=json.loads((HERE/'inherited/gap_fusion/coefficients/BINDING.json').read_text())
    require(binding['ports']==parent['ports'],'whole tuple differs from the parent binding')
    values={};raws={}
    for key,meta in binding['ports'].items():
        gz=(HERE/'coefficients'/meta['file']).read_bytes()
        raw=gzip.decompress(gz)
        require(hashlib.sha256(gz).hexdigest()==meta['gzip_sha256'],'gzip hash '+key)
        digest=hashlib.sha256(raw).hexdigest()
        require(digest==meta['raw_sha256']==PINNED_RAW[key],'raw/pinned hash '+key)
        require(gz==(HERE/'inherited/gap_fusion/coefficients'/meta['file']).read_bytes(),'parent byte mismatch '+key)
        values[key]=int.from_bytes(raw,'little');raws[key]=raw
        require(values[key].bit_length()==meta['bits'],'bit-length mismatch '+key)
    beta,k0,mc,mf=(values[k] for k in PORTS)
    require(beta%2==1 and beta>=31 and k0>0 and 0<mc<beta<mf<2*beta,'fixed-port domain box')
    recipe_dir=HERE/'coefficients/recipe'
    require(hashlib.sha256((recipe_dir/'k215_transitions.json').read_bytes()).hexdigest()==TRANSITION_SHA,
            'transition seed SHA-256 mismatch')
    recipe=load_module('positive_coefficient_recipe',recipe_dir/'build_coefficients.py')
    data=recipe.recipe()
    geometry=recipe.finite_audit(data)
    controller=recipe.padding_certificate(data)
    # Reconstruct the four values in memory. Do not call materialize(), which writes files.
    big=1<<recipe.D_BITS
    dc=sum(c<<(recipe.B_BITS*e) for e,c in data['dc'].items())
    dr=1<<(recipe.B_BITS*recipe.SHIFT)
    native_mf=4+sum(data['mu']<<(recipe.B_BITS*t) for t in (recipe.T1,recipe.T2))
    native_mf+=sum(1<<(recipe.B_BITS*t) for t,*_ in data['targets'])
    native_mf+=sum(c<<(recipe.B_BITS*e) for e,c in data['padding'].items())
    native_mc=big-1-sum(1<<(recipe.B_BITS*e) for e in data['E'] if e!=1)-(2<<(recipe.B_BITS*1063))
    reconstructed={'beta':big-1,'K0':dc+big*dr,'MC':native_mc,'MF':native_mf+big-1}
    for key,value in reconstructed.items():
        require(value==values[key],'finite coefficient recipe value mismatch '+key)
        require(value.to_bytes((value.bit_length()+7)//8,'little')==raws[key],'finite coefficient recipe bytes mismatch '+key)
    return values, {'bit_lengths':{k:v.bit_length() for k,v in values.items()},
                    'raw_sha256':PINNED_RAW,'transition_sha256':TRANSITION_SHA,
                    'geometry':geometry,'padding_controller':controller,
                    'recipe_bytes_match':True,'MF_is_already_shifted':True}


def evaluate(e,point,ports,modulus):
    env={k:v%modulus for k,v in ports.items()}
    env.update({k:v%modulus for k,v in point.items()})
    for n,op,x,y in e['source']:
        a=env[x] if isinstance(x,str) else x
        b=env[y] if isinstance(y,str) else y
        env[n]=(a+b if op=='+' else a-b if op=='-' else a*b)%modulus
    return env


def formula(point,ports,modulus,absorbed,sharp):
    p=modulus
    J,F,alpha,i,T,w,s,n,eta,zeta=(point[k]%p for k in WITNESSES)
    beta,K0,MC,MF=(ports[k]%p for k in PORTS)
    q=(beta*J+1)%p;g=(q-1)%p;X=w*q%p;Y=pow(q,3,p)*s%p
    C=(q-F-alpha)%p;B=((K0+w)*C-F)%p
    mu=(q*q+1)%p;A=(mu*Y*(X+1)+1)%p;Delta=(A*A-1)%p;H=(4*A-5)%p
    k=(eta+zeta)%p;c=(k*Y+eta)%p
    v0=X*pow(mu,2,p)*pow(Y,2,p)%p;D=(v0*(v0+1)*k*k+1)%p
    G=(g*(q-F)+alpha)%p;R=(G*(q*q-1)+(MC+q*MF)*J)%p;e=(k-R-1)%p
    E=i*c*c%p;Fs=(1+Delta*D*E*E)%p;Q=Delta*Delta*D*E*E%p;delta=(Q-1)%p
    b=(c*(T+alpha)-R)%p;V=(Fs*b-c)%p;Dnum=(Q*V*V-1)%p
    Gamma=A*D*E%p if sharp else 0
    M=g*mu*mu*H%p;Kpos=(X*(3*c-2*X)+2)%p
    padding=n if absorbed else (n+s)%p
    Z=(g*mu*mu*(H*(padding+V+Gamma-b*B)+Kpos)-H*(mu*mu*B+g*e))%p
    a=D*Fs%p;u=delta*M*M*a%p;v=M*M*Dnum%p
    N=((delta*Z*Z-v-u)**2-4*u*v)%p
    return {'q':q,'Y':Y,'Mtot':M,'Znum':Z,'N':N}


def ray_degree(e,ports,p,seed):
    rng=random.Random(seed)
    direction={k:rng.randrange(1,100) for k in WITNESSES}
    current=[evaluate(e,{k:t*v for k,v in direction.items()},ports,p)['N'] for t in range(518)]
    degree=0;top=current[0];factorial=1
    for j in range(1,518):
        current=[(current[i+1]-current[i])%p for i in range(len(current)-1)]
        if not any(current):
            return degree,top*pow(factorial,-1,p)%p,direction
        factorial=factorial*j%p;degree=j;top=current[0]
    raise Failure('ray degree exceeds the syntactic bound')


def leading(point,ports,p,sharp):
    q0=ports['beta']%p*point['J']%p
    k0=(point['eta']+point['zeta'])%p
    out=(1024 if sharp else -1024)%p
    factors=((q0,314 if sharp else 326),(point['i'],10),(point['w'],28 if sharp else 30),
             (point['s'],62 if sharp else 64),(k0,34),((point['T']+point['alpha'])%p,2))
    for base,exponent in factors:
        out=out*pow(base,exponent,p)%p
    return out


def main(output=None):
    values,coefficient_receipt=coefficients()
    degree_receipt=universal_degree_identities()
    builder=load_module('positive_quotient_builder',HERE/'build.py')
    receipts=[]
    for index,name in enumerate(NAMES):
        path=HERE/(name+'.json');e=json.loads(path.read_text())
        graph=validate_graph(e)
        parent_path=HERE/e['parent']
        require(hashlib.sha256(parent_path.read_bytes()).hexdigest()==e['parent_sha256'],'parent file hash mismatch')
        parent=json.loads(parent_path.read_text())
        absorbed='_absorbed' in name;sharp=name.endswith('_sharp')
        require(e==builder.build(absorbed,sharp),'deterministic builder replay differs')
        identities=symbolic_checks(e,parent)
        rng=random.Random(20261024+index)
        controls=0
        for p in PRIMES:
            for j in range(24):
                point={k:rng.randrange(-19,20) if j<12 else rng.randrange(1,40) for k in WITNESSES}
                actual=evaluate(e,point,values,p)
                independent=formula(point,values,p,absorbed,sharp)
                require(all(actual[k]==v for k,v in independent.items()),'independent full-formula mismatch')
                oldpoint={k:point[k] for k in parent['witnesses'] if k!='Y'}
                oldpoint['Y']=pow(actual['q'],3,p)*point['s']%p
                oldpoint['n']=(point['n']-point['s'])%p if absorbed else point['n']
                before=evaluate(parent,oldpoint,values,p)
                require(before['N']==pow(actual['q'],12,p)*actual['N']%p,'full parent polynomial identity mismatch')
                controls+=1
        rays=[]
        for j,p in enumerate(PRIMES):
            deg,top,point=ray_degree(e,values,p,700+index*10+j)
            predicted=leading(point,values,p,sharp)
            require(deg==e['exact_degree'] and top==predicted and predicted!=0,'degree or leading-form ray mismatch')
            rays.append({'prime_bits':p.bit_length(),'degree':deg,'top_coefficient':top,'predicted_top_coefficient':predicted})
        receipts.append({'name':name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                         **graph,**identities,'exact_degree':e['exact_degree'],
                         'signed_and_positive_full_formula_controls':controls,'rays':rays})
    # Deliberate transcription errors must be rejected by the exact checks.
    base=json.loads((HERE/'quotient_absorbed.json').read_text())
    parent=json.loads((HERE/base['parent']).read_text())
    mutations=[]
    for node,operand in [('Am1',1),('Znum',1),('fourfafc',2)]:
        bad=json.loads(json.dumps(base))
        row=next(r for r in bad['source'] if r[0]==node)
        row[operand]='+' if operand==1 else 3
        rejected=False
        try:
            symbolic_checks(bad,parent)
        except Failure:
            rejected=True
        require(rejected,'planted mutation survived: '+node)
        mutations.append(node)
    result={'status':'PASS','scope':'Finite syntax, coefficient and polynomial checks; ordinary equivalence proof is PROOF.md.',
            'coefficients':coefficient_receipt,'universal_degree_identities':degree_receipt,
            'equations':receipts,'rejected_mutations':mutations,
            'full_formula_controls':sum(x['signed_and_positive_full_formula_controls'] for x in receipts),
            'degree_rays':sum(len(x['rays']) for x in receipts),
            'exact_carrier_finalizer_identities':sum(x['exact_cut_identities'] for x in receipts)}
    if output is not None:
        Path(output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'equations':[{k:r[k] for k in ('name','operations','exact_degree')} for r in receipts],
                      'coefficient_recipe_bytes_match':True,'full_formula_controls':result['full_formula_controls'],
                      'degree_rays':result['degree_rays'],'exact_carrier_finalizer_identities':result['exact_carrier_finalizer_identities'],
                      'rejected_mutations':mutations},indent=2))
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='optional explicit JSON receipt path; otherwise read-only')
    args=parser.parse_args()
    main(args.output)
