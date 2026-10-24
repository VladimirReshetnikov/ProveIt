#!/usr/bin/env python3
"""Independent literal arithmetic checks and complete deterministic replay.

The arithmetic auditor imports only the inherited symbolic audit helper;
it does not import a constructor. The separate reproduction phase executes
the constructor, then compares every defining polynomial and certificate.
"""
from pathlib import Path
from copy import deepcopy
from collections import Counter
from fractions import Fraction
import argparse,hashlib,importlib.util,json,math,subprocess,sys,tempfile

ROOT=Path(__file__).resolve().parent
DEP=ROOT/'ConZFC_407_888_Quartics'
sys.path.insert(0,str(DEP/'code'))
from audit_new import Audit,atom,var,constant,add,mul,scale,require
sys.path.insert(0,str(DEP/'code/integer_pipeline'))
from verify_integer import domain
from verify_projection import verify as integer_projection
from independent_polynomial import verify_expansion
spec=importlib.util.spec_from_file_location('natural_check',DEP/'code/psd_contract/check.py')
natural=importlib.util.module_from_spec(spec);spec.loader.exec_module(natural)

def read(p):return json.loads(Path(p).read_text())
def normalize(x):return json.loads(json.dumps(x,sort_keys=True))
def named(d,name):
    ids=[i for i,x in enumerate(d['variables']) if x['name']==name]
    require(len(ids)==1,'missing/duplicate variable '+name)
    return ('v',ids[0])
def plus(a,b):return add(a,b)
def minus(a,b):return add(a,scale(b,-1))
def product(xs):
    r=constant(1)
    for x in xs:r=mul(r,x)
    return r

def arithmetic(d):
    a=Audit(d)
    powers={(atom(p['base']),atom(p['exponent'])):atom(p['output']) for p in d['powers']}
    bins={atom(p['output']):(atom(p['n']),atom(p['k'])) for p in d['binomials']}
    facts=d['factorial_graphs']
    interfaces={atom(p[k]) for p in d['powers'] for k in ('base','exponent','output')}
    interfaces.update(atom(f[k]) for f in facts for k in f)
    interfaces.update(atom(d['radix'][k]) for k in ('radix','radix_multiple'))
    def safe_expand(target,leaves):
        target=atom(target)
        stops={x[1]:var(x[1]) for x in interfaces if x[0]=='v' and x!=target}
        stops.update(leaves)
        return a.expand(target,stops)
    require(len(facts)==2 and len(bins)==3 and len(powers)==21,'macro counts')
    for i,f in enumerate(facts):
        n,h,out,C,V,r,s=[atom(f[k]) for k in ('input','half','output','binomial','numerator','remainder','slack')]
        hp,fp,np,cp,vp,rp,sp=map(var,range(-100,-107,-1))
        require(a.expand(n,{h[1]:hp})==add(scale(hp,2),constant(1)),'odd factorial input')
        require(C in bins and bins[C][1]==n,'factorial binomial output/index')
        require(a.expand(bins[C][0],{out[1]:fp,n[1]:np})==add(fp,np),'factorial binomial upper argument')
        matching=[(base,k) for (base,k),v in powers.items() if v==V]
        require(len(matching)==1 and matching[0][1]==n,'factorial numerator power')
        require(a.expand(matching[0][0],{out[1]:fp,h[1]:hp})==add(add(fp,hp),constant(1)),'centered numerator base')
        leaves={out[1]:fp,C[1]:cp,V[1]:vp,r[1]:rp,s[1]:sp}
        tag='centered_factorial'+str(i)
        require(a.row_poly(tag+'.floor',leaves)==minus(minus(vp,mul(cp,fp)),rp),'centered floor row')
        require(a.row_poly(tag+'.remainder_bound',leaves)==minus(minus(minus(cp,rp),sp),constant(1)),'centered denominator bound')
    rd=d['radix'];B=atom(rd['radix_multiple']);q=atom(rd['radix'])
    Vsum=atom(rd['factorial_radix']['numerator'])
    leaves={B[1]:var(-110)}
    want=constant(1)
    for i,f in enumerate(facts):
        V=atom(f['numerator']);leaves[V[1]]=var(-111-i);want=add(want,var(-111-i))
    require(a.expand(q,leaves)==mul(var(-110),want),'sum of both factorial numerators in radix')
    require([atom(x) for x in rd['factorial_radix']['factorial_numerators']]==[atom(x['numerator']) for x in facts],'factorial numerator inventory')
    require(atom(rd['factorial_radix']['H'])==atom(facts[0]['input']),'H source order')
    require(all(a.positive(p['exponent']) for p in d['powers']),'power exponent positivity')
    # Literal exact digit and divisibility interfaces.
    for i,b in enumerate(d['binomials']):
        n,k,C=map(atom,(b['n'],b['k'],b['output']))
        qplus=[base for (base,kk),out in powers.items() if kk==n and safe_expand(base,{q[1]:var(-120)})==add(var(-120),constant(1))]
        require(len(qplus)==1,'exact binomial numerator base')
        num=powers[(qplus[0],n)];den=powers[(q,k)]
        h,r,rs,os=[named(d,'choose'+str(i)+'.'+s) for s in ('high','remainder','rslack','oslack')]
        anchors=[q,C,num,den,h,r,rs,os]
        leaves={x[1]:var(-121-j) for j,x in enumerate(anchors)}
        Q,Cc,N,D,H,R,RS,OS=[leaves[x[1]] for x in anchors]
        require(a.row_poly('choose'+str(i)+'.digit',leaves)==minus(minus(N,mul(D,add(mul(Q,H),Cc))),R),'exact binomial digit row')
        require(a.row_poly('choose'+str(i)+'.remainder_bound',leaves)==minus(minus(minus(D,R),RS),constant(1)),'exact binomial remainder')
        require(a.row_poly('choose'+str(i)+'.digit_bound',leaves)==minus(minus(minus(Q,Cc),OS),constant(1)),'exact binomial digit bound')
    for i,(n,k,bb,label) in enumerate(d['ranges']):
        n,k,bb=map(atom,(n,k,bb));require(bb==B,'range common modulus')
        require(a.positive(n) and a.positive(k),'range positive arguments')
        qplus=[base for (base,kk),out in powers.items() if kk==n and safe_expand(base,{q[1]:var(-120)})==add(var(-120),constant(1))]
        require(len(qplus)==1,'range numerator base')
        num=powers[(qplus[0],n)];den=powers[(q,k)]
        h,r,s=[named(d,'range'+str(i)+'.'+x) for x in ('quotient','remainder','slack')]
        anchors=[B,num,den,h,r,s]
        leaves={x[1]:var(-130-j) for j,x in enumerate(anchors)}
        BB,N,D,H,R,S=[leaves[x[1]] for x in anchors]
        require(a.row_poly(label+'.quotient_multiple',leaves)==minus(minus(N,product([D,BB,H])),R),'range quotient')
        require(a.row_poly(label+'.remainder_bound',leaves)==minus(minus(minus(D,R),S),constant(1)),'range remainder')
    # Independent checks for every requested power and Pell-index addition.
    indices={atom(x['exponent']):tuple(map(atom,x['pair'])) for x in d['indices']}
    seeds={atom(x['exponent']):tuple(map(atom,x['pair'])) for x in d['seeds']}
    derivations={atom(x['target']):x for x in d['derivations']}
    require(set(indices)=={k for n,k in powers},'all exponent coordinates')
    require(set(seeds).isdisjoint(derivations) and set(seeds)|set(derivations)==set(indices),'seed partition')
    A=atom(d['scale'][1])
    for target,rec in derivations.items():
        require(rec['kind']=='shift' and rec['shift'] in(1,2),'derived index kind')
        source=atom(rec['source']);X,Y=indices[source];Xp,Yp=indices[target]
        ap,xp,yp,kp=map(var,(-140,-141,-142,-143))
        require(a.expand(target,{source[1]:kp})==add(kp,constant(rec['shift'])),'exponent shift')
        dd=minus(mul(ap,ap),constant(1))
        u,v=(ap,constant(1)) if rec['shift']==1 else (add(scale(dd,2),constant(1)),scale(ap,2))
        leaves={A[1]:ap,X[1]:xp,Y[1]:yp}
        require(a.expand(Xp,leaves,True)==add(mul(xp,u),product([dd,yp,v])),'derived Pell X')
        require(a.expand(Yp,leaves,True)==add(mul(xp,v),mul(yp,u)),'derived Pell Y')
    base_records={}
    for row in d['rows']:
        if row['label'].startswith('base') and row['label'].endswith('.T_definition'):
            tag=row['label'].split('.')[0]
            T=named(d,tag+'.T')
            matches=[]
            for base in {n for n,k in powers}:
                ap,np,tp=map(var,(-150,-151,-152))
                leaves={bb[1]:var(bb[1]) for bb in {n for n,k in powers}}
                leaves.update({A[1]:ap,base[1]:np,T[1]:tp})
                want=minus(minus(minus(scale(mul(ap,np),2),tp),mul(np,np)),constant(1))
                if a.row_poly(row['label'],leaves)==want:matches.append(base)
            require(len(matches)==1,'power base interface')
            base_records[matches[0]]=T
    require(set(base_records)=={n for n,k in powers},'power base coverage')
    for i,p in enumerate(d['powers']):
        n,k,m=map(atom,(p['base'],p['exponent'],p['output']))
        X,Y=indices[k];T=base_records[n];qq=named(d,'pow'+str(i)+'.quotient')
        atoms=[n,m,X,Y,T,qq,A];leaves={x[1]:var(-160-j) for j,x in enumerate(atoms)}
        N,M,XX,YY,TT,QQ,AA=[leaves[x[1]] for x in atoms]
        want=minus(minus(minus(add(XX,mul(YY,N)),mul(YY,AA)),M),mul(TT,QQ))
        require(a.row_poly('pow'+str(i)+'.power_congruence',leaves)==want,'power congruence')
    return {'factorial_graphs':2,'literal_factorial_rows':4,'power_graphs':len(powers),
        'distinct_bases':len(base_records),'seed_indices':len(seeds),'derived_indices':len(derivations),
        'exact_binomial_graphs':len(bins),'range_divisibilities':len(d['ranges']),
        'all_power_exponents_positive':True,'centered_sum_radix_binding':True}

def fixtures():
    cases=0;truecases=0;bounds=0
    for n in range(21):
        fac=math.factorial(n)
        choices=set(range(501))|{fac-1,fac,fac+1,2*fac,10*fac}
        for f in sorted(x for x in choices if x>=0):
            num=(2*f+n+1)**n;den=2**n*math.comb(f+n,n)
            require((num//den==f)==(f==fac),'centered fixed-point fixture')
            cases+=1
        f=fac
        require(0<=Fraction((2*f+n+1)**n,2**n*math.comb(f+n,n))-fac<1,'factorial true error')
        truecases+=1
    for n in range(1,42,2):
        for f in range(101):
            m=f+(n+1)//2;V=m**n
            for j in range(n+1):
                require(math.comb(f+n,j)<=V,'unconditional lower digit bound')
                bounds+=1
    return {'fixedpoint_pairs':cases,'true_factorial_cases':truecases,'lower_digit_inequalities':bounds}

def main(output,receipt=None,full=True):
    output=Path(output)
    d=read(output/'raw_audit_input.json');src=read(output/'equation.json')
    res={'status':'PASS','optimized_python':not __debug__,'arithmetic':arithmetic(d),'fixtures':fixtures(),'equations':{}}
    mutations=0
    for mode in ('floor','radix','odd'):
        bad=deepcopy(d)
        if mode=='floor':
            row=next(r for r in bad['rows'] if r['label']=='centered_factorial0.floor')
            row['terms'][0][0]+=1
        elif mode=='radix':
            bad['radix']['radix']=bad['factorial_graphs'][0]['numerator']
        else:bad['factorial_graphs'][0]['input']=['c',2]
        try:arithmetic(bad)
        except (ValueError,KeyError):mutations+=1
        else:raise ValueError('corrupted arithmetic accepted: '+mode)
    for name in ('natural_cap16','natural_cap64'):
        p=output/name;target=read(p/'equation.json');cert=read(p/'elimination_certificate.json')
        r,terms=natural.verify(src,target,cert);require(terms==read(p/'expanded_polynomial.json')['terms'],'natural expansion')
        res['equations'][name]=r
    for name in ('integer_cap16',):
        p=output/name;signed=read(p/'guarded.json');conv=read(p/'domain_conversion.json')
        target=read(p/'equation.json');cert=read(p/'elimination_certificate.json')
        res['equations'][name]={'domain':domain(src,signed,conv),
            'projection':integer_projection(signed,target,cert),
            'expansion':verify_expansion(target,read(p/'expanded_polynomial.json'))}
    res['negative_controls_rejected']=mutations
    if full:
        prefix=[sys.executable]+([] if __debug__ else ['-O'])
        with tempfile.TemporaryDirectory(prefix='centered-factorial-replay-') as tmp:
            subprocess.run(prefix+[str(ROOT/'centered_factorial_build.py'),'--output',tmp],check=True,capture_output=True)
            subprocess.run(prefix+[str(DEP/'code/integer_pipeline/build_integer.py'),
                '--source',str(Path(tmp)/'equation.json'),'--output',str(Path(tmp)/'integer_cap16'),'--max-support','16'],
                check=True,capture_output=True)
            count=0
            for directory,filenames in [('', ['equation.json','expanded_polynomial.json','raw_audit_input.json']),
                ('natural_cap16',['equation.json','expanded_polynomial.json','elimination_certificate.json']),
                ('natural_cap64',['equation.json','expanded_polynomial.json','elimination_certificate.json']),
                ('integer_cap16',['equation.json','expanded_polynomial.json','elimination_certificate.json',
                    'domain_conversion.json','guarded.json'])]:
                for name in filenames:
                    require(read(Path(tmp)/directory/name)==read(output/directory/name),'deterministic replay differs: '+directory+'/'+name)
                    count+=1
            res['reproduced_defining_files']=count
    res['scope']='Exact literal arithmetic interfaces, independent domain/projection/expansion checks, and complete reproduction. Universal proofs are in centered_factorial_proof.md and the identified inherited source.'
    if receipt:Path(receipt).write_text(json.dumps(res,sort_keys=True,indent=2)+'\n')
    print(json.dumps(res,sort_keys=True,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'centered_output')
    p.add_argument('--receipt',type=Path);p.add_argument('--skip-reproduction',action='store_true')
    args=p.parse_args();main(args.output,args.receipt,not args.skip_reproduction)

