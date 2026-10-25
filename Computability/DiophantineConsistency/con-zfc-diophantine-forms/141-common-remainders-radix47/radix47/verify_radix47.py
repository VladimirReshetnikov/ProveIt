"""Standalone verifier for complemented-label radix47. No generator imports."""
from pathlib import Path
from collections import Counter
from copy import deepcopy
import gzip,hashlib,json,math

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'radix47'

def check(p,s):
    if not p:raise ValueError(s)

def binary_power(a,n,m):
    r=1
    while n:
        if n%2:r=r*a%m
        a=a*a%m;n//=2
    return r

def prime_certificate(p):
    check(type(p)is int and p>=2,'prime integer')
    for k in range(2,math.isqrt(p)+1):check(p%k!=0,'primality')
    return {'prime':p,'all_trial_divisors_checked_through':math.isqrt(p)}

def exact_order(a,n,m,primes):
    check(binary_power(a,n,m)==1,'annihilating power')
    rem=n
    for p in primes:
        prime_certificate(p)
        check(rem%p==0,'order factor')
        while rem%p==0:rem//=p
    check(rem==1,'complete order factorization')
    proper={str(p):binary_power(a,n//p,m) for p in primes}
    check(all(r!=1 for r in proper.values()),'maximal proper order')
    return {'modulus':m,'base_residue':a,'order':n,'maximal_proper_power_residues':proper}

def expected_coefficients():
    tiles=json.loads((ROOT/'sources/research/indexed-tile-enumeration/TILES.json').read_text())
    result=[0]*3297
    for j,t in enumerate(tiles):
        u=sum(v*(1<<s) for v,s in zip(t,[0,8,17,25]))
        check(0<=u<(1<<34),'label packing')
        result[j]=1+1024*(u+1)
    groups=[(1023,8,10),(1003,8,27),(1013,9,18),(983,9,35)]
    for start,count,shift in groups:
        for j in range(count):
            check(result[start+j]==0,'disjoint control')
            result[start+j]=2**(shift+j)
    for e in [992,1011,1022,1031,1095,2195,3296]:
        check(result[e]==0,'disjoint marker');result[e]=2**44
    return result

def validate(c,values,certificate):
    check(c==expected_coefficients(),'complete Phi coefficients')
    b=47;L=8807;rho=2**b;B=2**(b*L)
    phirev=0
    for ce in c:phirev=phirev*rho+ce
    K=(rho**1097+rho**2199)*phirev+sum(rho**e for e in [30,62,1100,2201,8849])
    occupied=[j for j,ce in enumerate(c) if ce]
    MC=B-1+rho-(rho+3)*rho**1063-sum(rho**e for e in occupied)
    core=rho**1013*sum(rho**j for j in range(10))+rho**1065*sum(rho**j for j in range(9))+rho**2195+rho**3296
    MF=2*B+3+(2**47-2)*(rho**4393+rho**5495)+core-rho**8792+(2**28-3)*rho**7694-rho**7691
    check(values=={'beta':B-1,'K0':K,'MC':MC,'MF':MF},'entire coherent tuple')
    check(MC.bit_count()==47*L-986 and (MF-B+1).bit_count()==986,'mask populations')
    check(certificate['radix_bits']==47 and certificate['d']==413929 and certificate['spacing']==101269,'certificate model')
    lam=certificate['selected']['candidate'];kap=lam-1
    check(lam==1012691 and lam>47*L and kap%101269==0,'controller spacing and lambda')
    primes=[prime_certificate(p) for p in [47,8807,lam]]
    order_certs=[exact_order(B%47,23,47,[23]),exact_order(B%8807,4403,8807,[7,17,37]),exact_order(B%lam,1012690,lam,[2,5,7,17,23,37])]
    check(binary_power(2,47*L*kap,lam*lam)==285921151559,'valuation-one lift')
    check(285921151559==1+282338*lam and 282338%lam!=0,'nonzero lift quotient')
    desired=[(47,17),(8807,5042),(lam,834350)]
    assoc=[]
    for m,h in desired:
        r=binary_power(2,47,m);bb=binary_power(2,47*L,m)
        kk=sum(binary_power(r,e,m) for e in [30,62,1100,2201,8849])
        kk+=sum(ce*(binary_power(r,4393-e,m)+binary_power(r,5495-e,m)) for e,ce in enumerate(c))
        kk%=m
        hh=(1+bb*kk+bb*bb)%m
        check(kk==K%m and hh==h,'complete bracket association')
        check(math.gcd(h,m)==1,'bracket unit')
        check(math.gcd(bb*bb-1,m)==1,'square unit')
        assoc.append({'modulus':m,'B':bb,'K':kk,'Hctrl':hh})
    expected_fixed=[dict(row,rho=binary_power(2,47,row['modulus'])) for row in assoc[:2]]
    check(certificate['fixed']==expected_fixed,'reported fixed residues')
    selected=certificate['selected']
    fs=[[2,1],[5,1],[7,1],[17,1],[23,1],[37,1]]
    expected_selected=dict(assoc[-1],candidate=lam,index=10,rho=binary_power(2,47,lam),order=1012690,order_factors=fs,lambda_minus_one_factors=fs,lift_residue=285921151559,lift_quotient=282338,result='found')
    check(selected==expected_selected,'reported selected certificate')
    prefix=[]
    for m in range(5,10):
        p=101269*m+1
        divisor=next(k for k in range(2,math.isqrt(p)+1) if p%k==0)
        prefix.append({'index':m,'candidate':p,'least_factor':divisor,'result':'composite'})
    check(certificate['search']==prefix+[selected] and certificate['outcome']=='found','reported bounded prefix')
    return {'primality':primes,'orders':order_certs,'lift_residue':285921151559,'lift_quotient':282338,'brackets':assoc}

def validate_geometry(c,record):
    rho=2**47;M=2**44
    check(max(c)==M and max(c[:943])==15049678914561,'actual coefficient maximum')
    check(sum(c)==3953059820717999,'actual complete coefficient sum')
    check(sum(c)+2*M+5+3*rho//4+29<30*rho,'carry29 invariant')
    check(88*M+rho-1024+2*M+5+3*rho//4+29<13*rho,'carry12 refinement')
    check(943+29<1024 and 7*M-1024+12<rho,'bootstrap and clause reset')
    E=set(i for i,x in enumerate(c) if x)|{1063,1064}
    kernel={}
    for e,ce in enumerate(c):
        if ce:
            for a in [4393,5495]:
                check(a-e not in kernel,'reflected residue uniqueness');kernel[a-e]=ce
    for e in [30,62,1100,2201]:
        check(e not in kernel,'bare residue uniqueness');kernel[e]=1
    check(42 not in kernel,'spatial residue uniqueness')
    def linear(t):return [[e,kernel[t-e]] for e in sorted(E) if t-e in kernel]
    targets=set(range(1013,1023))|set(range(1065,1074))|{2194,2195,3295,3296,1012,1064,4392,4393,5494,5495,7690,8791}|set(range(7691,7696))|set(range(8792,8807))
    check(set(row['target'] for row in record['claims'])==targets and len(record['claims'])==len(targets),'complete target coverage')
    for row in record['claims']:check(row['terms']==linear(row['target']),'complete target linear form')
    check(linear(2194)==[] and linear(3295)==[[2195,1]],'anchor reset identities')
    check(linear(7690)==[[2195,c[0]]] and linear(8791)==[[3296,c[0]]],'padding reset identities')
    check(all(linear(t)==[] for t in list(range(7691,7696))+list(range(8792,8807))),'padding zero identities')
    for j in range(10):check(linear(1013+j)==[[983+j,1]],'north copy identity')
    for j in range(9):check(linear(1065+j)==[[1003+j,1]],'spatial copy identity')
    check(all(e-f!=1102 for e in E for f in E),'disjoint clause hit sets')
    check([(e,f) for e in sorted(E) for f in sorted(E) if e-f==1101]==[(3296,2195)],'unique anchor difference')
    check((rho-2).bit_count()*2+22+15*47+3*47+26==986,'complete population budget')
    return {'predecoded_carry_cap':29,'decoded_carry_cap':12,'tested_target_identities':len(targets),'padding_population':872,'all_physical_positions_retained':len(E)==986}

def exact_ray(p,values,modulus):
    def trim(a):
        while len(a)>1 and a[-1]==0:a.pop()
        return a
    def add(a,b,sign=1):
        v=[0]*max(len(a),len(b))
        for k,x in enumerate(a):v[k]=x
        for k,x in enumerate(b):v[k]=(v[k]+sign*x)%modulus
        return trim(v)
    def mul(a,b):
        v=[0]*(len(a)+len(b)-1)
        for j,x in enumerate(a):
            for k,y in enumerate(b):v[j+k]=(v[j+k]+x*y)%modulus
        return trim(v)
    v={w:[0,1] for w in p['witnesses']};v.update({k:[a%modulus] for k,a in values.items()})
    known=set(v);dependencies={}
    for name,op,a,b in p['source']:
        check(name not in known,'circuit name uniqueness')
        aa=[a%modulus] if type(a)is int else v[a];bb=[b%modulus] if type(b)is int else v[b]
        v[name]=mul(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
        dependencies[name]=[x for x in [a,b] if type(x)is str];known.add(name)
    live=set();stack=[p['output']]
    while stack:
        x=stack.pop()
        if x not in live:live.add(x);stack.extend(dependencies.get(x,[]))
    check(set(p['witnesses'])|{r[0] for r in p['source']}<=live,'all witnesses and gates live')
    check(len(p['source'])==66,'66 live operations')
    check(len(v[p['output']])-1==157,'attained degree157')
    lead=pow(2,17,modulus)*pow(values['beta']%modulus,91,modulus)%modulus
    check(lead!=0 and v[p['output']][-1]==lead,'exact leading ray coefficient')
    expected={'N0':22,'N1':18,'Na':62,'Nk':7,'Nt':2,'scaled_Ns':46}
    for name,deg in expected.items():check(len(v[name])-1==deg,'factor degree '+name)
    return {'modulus':modulus,'attained_degree':157,'leading_ray_coefficient':lead,'factor_degrees':expected,'counts':dict(Counter(r[1] for r in p['source']))}

def main():
    ledger=json.loads((ROOT/'DEPENDENCIES.json').read_text())
    for name,rec in ledger['files'].items():
        b=(ROOT/name).read_bytes()
        check(len(b)==rec['bytes'] and hashlib.sha256(b).hexdigest()==rec['sha256'],'retained source byte identity')
    report=json.loads((OUT/'construction_report.json').read_text())
    values={}
    for name,rec in report['binding'].items():
        compressed=(OUT/rec['file']).read_bytes();raw=gzip.decompress(compressed)
        check(hashlib.sha256(raw).hexdigest()==rec['raw_sha256'],'raw coefficient checksum')
        check(hashlib.sha256(compressed).hexdigest()==rec['gzip_sha256'],'gzip coefficient checksum')
        values[name]=int.from_bytes(raw,'little')
        check(values[name].bit_length()==rec['bits'] and len(raw)==rec['raw_bytes'],'coefficient length')
    c=json.loads((OUT/'phi_coefficients.json').read_text())
    certificates=validate(c,values,report['controller'])
    geom=json.loads((OUT/'native_geometry.json').read_text())
    geometry=validate_geometry(c,geom)
    p=json.loads((OUT/'polynomial.json').read_text())
    parent=json.loads((ROOT/'sources/candidates/one-page-compact66-radix55/polynomial.json').read_text())
    check(p['source']==parent['source'] and p['witnesses']==parent['witnesses'],'entire inherited P66 circuit')
    rays=[exact_ray(p,values,m) for m in [1000000007,1000000009]]
    controls=[]
    mutations=[]
    for label,idx in [('wrong marker',2195),('omitted selector',500),('missing control',1018),('polluted zero',2000)]:
        cc=c[:];cc[idx]+=1
        mutations.append((label,cc,values,report['controller'],'complete Phi coefficients'))
    for name in values:
        vv=dict(values);vv[name]+=1
        mutations.append(('wrong '+name,c,vv,report['controller'],'entire coherent tuple'))
    rc=deepcopy(report['controller']);rc['selected']['candidate']=1012693
    mutations.append(('wrong controller prime',c,values,rc,'controller spacing and lambda'))
    for key in ['order','lift_residue','lift_quotient','Hctrl','K','B']:
        rc=deepcopy(report['controller']);rc['selected'][key]+=1
        mutations.append(('wrong reported '+key,c,values,rc,'reported selected certificate'))
    rc=deepcopy(report['controller']);rc['fixed'][0]['modulus']=49
    mutations.append(('wrong fixed prime',c,values,rc,'reported fixed residues'))
    for label,cc,vv,rc,reason in mutations:
        try:validate(cc,vv,rc)
        except ValueError as ex:
            check(str(ex)==reason,'specific mutation rejection');controls.append({'mutation':label,'rejection':reason})
        else:raise ValueError('mutation accepted: '+label)
    for label,change in [('omitted target',lambda x:x['claims'].pop()),('wrong reset coefficient',lambda x:x['claims'][0]['terms'][0].__setitem__(1,2))]:
        altered=deepcopy(geom);change(altered)
        try:validate_geometry(c,altered)
        except ValueError as ex:controls.append({'mutation':label,'rejection':str(ex)})
        else:raise ValueError('geometry mutation accepted')
    output={'status':'PASS','retained_source_files_verified':len(ledger['files']),'certificates':certificates,'geometry':geometry,'exact_rays':rays,'negative_controls':controls,'negative_control_count':len(controls),'byte_order':'little','raw_coefficient_bytes':sum(x['raw_bytes'] for x in report['binding'].values()),'scope':'Exact finite construction, controller, native support identities and circuit checks; unbounded proof is separate.'}
    (OUT/'verification_report.json').write_text(json.dumps(output,indent=2,sort_keys=True)+'\n')
    print(json.dumps(output,indent=2,sort_keys=True))

if __name__=='__main__':main()
