#!/usr/bin/env python3
"""Independent finite source/circuit audit. All checks remain active under -O.
Unbounded consistency equivalence is proved in PROOF.md and its dependencies.
"""
from pathlib import Path
from collections import defaultdict,Counter
import copy,gzip,hashlib,itertools,json,random
import build_composed as construct
from circuit import evaluate

R=Path(__file__).resolve().parent

def require(p,msg):
    if not p:raise ValueError(msg)

def add(a,b,sign=1):
    c=dict(a)
    for m,v in b.items():c[m]=c.get(m,0)+sign*v
    return {m:v for m,v in c.items() if v}
def mul(a,b):
    c=defaultdict(int)
    for m,v in a.items():
        for n,t in b.items():c[tuple(i+j for i,j in zip(m,n))]+=v*t
    return {m:v for m,v in c.items() if v}
def source_rows():
    src=json.loads((R/'data/source_system65.json').read_text());names=src['variables']+src['constants'];n=31;z=(0,)*35
    env={s:{tuple(int(j==i) for j in range(35)):1} for i,s in enumerate(names)}
    def get(v):return ({z:v} if v else {}) if type(v) is int else env[v]
    for name,op,a,b in src['source']:env[name]=mul(get(a),get(b)) if op=='*' else add(get(a),get(b),-1 if op=='-' else 1)
    rows=[add(get(a),get(b),-1) for a,b in src['comparisons']]
    original=copy.deepcopy(rows);rows[13]=add(rows[13],rows[1]);rows[14]=add(rows[14],rows[2])
    require(add(rows[13],rows[1],-1)==original[13] and add(rows[14],rows[2],-1)==original[14],'inverse row operations')
    out=[]
    for row in rows:
        block=defaultdict(dict)
        for mon,c in row.items():
            p=tuple(i for i,e in enumerate(mon[:n]) for _ in range(e));require(len(p)<=2,'quadratic source')
            fac=2 if len(p)!=2 or p[0]==p[1] else 1
            block[p][mon[n:]]=c*fac
        out.append(dict(block))
    return out

def audit_source(layout,kerneldata):
    rows=source_rows();w=layout['weights'];qmap=dict(zip(layout['order'],layout['targets']))
    require(len(w)==31 and len(set(w))==31 and min(w)>0,'positive distinct positions')
    require(sorted(qmap)==list(range(1,23)) and len(set(qmap.values()))==22,'target numbering')
    kernels=[]
    for d,layer in enumerate(kerneldata['kernels']):
        require(layer['degree']==d,'layer order')
        k={t['exponent']:{tuple(c['powers']):c['coefficient'] for c in t['coefficient']} for t in layer['terms']}
        require(len(k)==len(layer['terms']) and min(k)>=0,'kernel positions');kernels.append(k)
    mons=[[()],[(i,) for i in range(31)],list(itertools.combinations_with_replacement(range(31),2))]
    checks=0
    for r,q in qmap.items():
        for d in range(3):
            for mon in mons[d]:
                got=kernels[d].get(q-sum(w[i] for i in mon),{});wanted=rows[r-1].get(mon,{})
                require(got==wanted,f'exact target coefficient row={r} monomial={mon}');checks+=1
    owners=[defaultdict(list) for _ in range(3)]
    for r,q in qmap.items():
        for mon in rows[r-1]:owners[len(mon)][q-sum(w[i] for i in mon)].append([r,list(mon)])
    require(all(set(kernels[d])==set(owners[d]) for d in range(3)),'no unowned coefficient taps')
    deg=[max(k) for k in kernels];W=max(w);H=max(deg[d]+d*W for d in range(3));Q=max(qmap.values())
    require(deg==layout['kernel_degrees'] and H==layout['convolution_height'] and W==layout['max_weight'] and Q==layout['maximum_target'],'source degrees')
    require(kernels[2][deg[2]]=={(0,0,0,0):1},'positive quadratic leader')
    require(deg[2]+W-deg[1]>=18 and deg[2]+2*W-deg[0]>=442,'unconditional source positivity gaps')
    require(H-Q>=32,'sparse target headroom')
    bits=[1064921,1070004,1064921,1064922]
    maxbound=max(sum(abs(c)*(1<<sum(e*b for e,b in zip(mon,bits))) for mon,c in co.items()) for k in kernels for co in k.values())
    require(maxbound.bit_length()==2134927,'coefficient bound')
    share=[{'degree':d,'exponent':e,'owners':v} for d,layer in enumerate(owners) for e,v in layer.items() if len(v)>1]
    return {'source_rows':22,'target_identities':22,'coefficient_checks':checks,'weighted_source_records':sum(len(x) for x in rows),'unique_taps':sum(len(k) for k in kernels),'shared_taps':share,'W':W,'H':H,'Q':Q,'kernel_degrees':deg}

def fixed_values(body):
    binding=json.loads((R/'coefficients/COEFFICIENT_BINDING.json').read_text())
    vals={}
    for rec in binding['files']:
        raw=gzip.decompress((R/'coefficients'/rec['file']).read_bytes())
        require(hashlib.sha256(raw).hexdigest()==rec['sha256'],'fixed native payload hash')
        vals[rec['port']]=int.from_bytes(raw,'little')
    ports=[vals['beta'],vals['K'],vals['MC'],vals['MF_source']]
    used={n['name'] for n in body['nodes'] if n['kind']=='fixed'}
    out={}
    for rec in body['coefficient_recipes']:
        if rec['name'] not in used:continue
        value=0
        for t in rec['terms']:
            term=t['coefficient']
            for p,e in zip(ports,t['powers']):term*=p**e
            value+=term
        out[rec['name']]=value
    out['base_scale']=1<<body['base_scale_exponent']
    out['threshold_scale']=1<<body['threshold_scale_exponent']
    require(set(out)==used,'complete fixed coefficient binding')
    return ports,out

def direct(body,vs,ports,fixed,p):
    v=dict(vs)
    if body['domain']=='positive integers':v['j']-=1
    else:
        for x in v:
            if x!='j':v[x]+=1
    b,g,h,s,w,C,i,j,n=[v[x]%p for x in body['variables']]
    layout=json.loads((R/'data/layout.json').read_text())
    ks=json.loads((R/'data/kernels.json').read_text())
    B=fixed['base_scale']*b*b%p;W=116
    def coefficient(co):
        return sum(t['coefficient']*product(pow(a,e,p) for a,e in zip(ports,t['powers'])) for t in co)%p
    ds=[sum(coefficient(t['coefficient'])*pow(B,t['exponent'],p) for t in k['terms'])%p for k in ks['kernels']]
    ell=sum(pow(B,x,p) for x in layout['weights'])%p
    targets=sum(pow(B,x,p) for x in layout['targets'])%p
    us=(ell+g)%p;gs=((ds[2]*us+ds[1])*us+ds[0])%p;N0=pow(B,117,p)
    mask=(N0-1-(b-1)*ell)%p;Sc=(g+N0*(2*gs+targets))%p;Tc=(mask+N0*(B-2)*targets)%p
    L=b*pow(B,1991,p)%p;RR=(L*(Sc+Tc+1)-Sc-1)%p
    NN=fixed['threshold_scale']*b*pow(B,1057,p)%p
    U=NN*NN*w%p;Y=NN*NN*s%p;M=RR*Y%p;P=2*M*M*U%p;K=(RR+1+h*(P-1))%p;A=M*(U+1)%p
    B1=(2*RR+1)%p;W1=b*w%p;J=(4*A-5)%p;Q=(3*W1*C-2*(W1*W1-1))%p
    D=((A*A-1)*C*C+1)%p;e=i*J*C%p;E=e*D*C%p;F=((A*A-1)*E*E+1)%p
    lm=(C*D+1-A)%p;G=(A+F*lm)%p;H=(C+F*(B1+j*C))%p;I=((G*G-1)*H*H+1)%p
    a0=((P*P-1)*K*K+1)%p;a1=4096**2*D*F*I%p;t=b*pow(B,W,p)%p
    margin=(K*K*(4*t-g)-16*t*(C-K*Y)**2)%p;V0=P*K%p
    Ns=(2*G+lm)%p
    N1=(2*e*e*D*(D-1)*lm+3*C)%p;N2=2*e*e*(D-1)*lm%p;N3=2*e*e*(lm-C)%p;N4=2*e*e*C%p
    T=(e*((2048*D*D-1024*D-256)*Ns-128*N1-80*N2-56*N3-42*N4+i*i*(1568-448*A+288*C))+640*i+4096)%p
    V1=T*H%p;om=J*margin%p;e0=(J*(n+W1*W1)+Q)%p;theta=(e0-om*(V0+V1))%p
    ans=((theta*theta-om*om*(a0+a1))**2-4*pow(om,4,p)*a0*a1)%p
    return ans,D

def product(xs):
    z=1
    for x in xs:z*=x
    return z

def check_chain(before,after,certificate):
    # Exact symbolic exponent proof for every replaced multiplication.
    known={1}
    for e,a,b in certificate['chain']:
        require(a in known and b in known and e==a+b and e not in known,'invalid exponent addition')
        known.add(e)
    require(set(certificate['required_exponents'])<=known,'missing required exponent')
    # Exact structural comparison uses a shared tuple interning table, not hashes.
    intern={}
    def node(v):
        if v not in intern:intern[v]=len(intern)
        return intern[v]
    def canon(body):
        B=body['named_nodes']['B'];powers=[]
        for k,x in enumerate(body['nodes']):
            if k==B:e=1
            elif x['kind']=='literal' and x['value']==1:e=0
            elif x['kind']=='mul' and powers[x['left']] is not None and powers[x['right']] is not None:e=powers[x['left']]+powers[x['right']]
            else:e=None
            powers.append(e)
        def rec(k,memo,usepowers):
            if k in memo:return memo[k]
            x=body['nodes'][k];e=powers[k]
            if usepowers and e is not None and e>0:f=('Bpower',e)
            elif x['kind'] in ('variable','fixed'):f=(x['kind'],x['name'])
            elif x['kind']=='literal':f=('literal',x['value'])
            else:
                a,b=rec(x['left'],memo,usepowers),rec(x['right'],memo,usepowers)
                if x['kind'] in ('add','mul'):a,b=sorted((a,b))
                f=(x['kind'],a,b)
            memo[k]=node(f);return memo[k]
        return rec(B,{},False),rec(body['output'],{},True)
    require(canon(before)==canon(after),'structural exponent-rewrite mismatch')

def main():
    import subprocess,sys
    from rewrite_powers import rewrite
    source=audit_source(json.loads((R/'data/layout.json').read_text()),json.loads((R/'data/kernels.json').read_text()))
    # Mutate an actually shared coefficient and require rejection.
    bad=json.loads((R/'data/kernels.json').read_text());share=source['shared_taps'][0]
    term=next(t for t in bad['kernels'][share['degree']]['terms'] if t['exponent']==share['exponent'])
    term['coefficient'][0]['coefficient']+=1
    rejected=False
    try:audit_source(json.loads((R/'data/layout.json').read_text()),bad)
    except ValueError:rejected=True
    require(rejected,'shared coefficient negative control')
    majorant=subprocess.run([sys.executable,str(R/'check_majorant.py')],capture_output=True,text=True,check=True)
    rng=random.Random(781311);variants={};replays=0
    for positive in (True,False):
        name='composed9_'+('positive' if positive else 'natural')
        raw=json.loads((R/f'generated/{name}_pre_rewrite.json').read_text());body=json.loads((R/f'generated/{name}.json').read_text());cert=json.loads((R/f'generated/{name}_certificate.json').read_text())
        chain=json.loads((R/f'generated/{name}_power_chain.json').read_text());degree=json.loads((R/f'generated/{name}_degree.json').read_text())
        rb=construct.build('shared_taps',positive,False,'horner','additive');rout,rc=rewrite(rb)
        rb=json.loads(json.dumps(rb));rout=json.loads(json.dumps(rout));rc=json.loads(json.dumps(rc))
        # Exact-degree annotation is intentionally outside the polynomial builder.
        require({k:v for k,v in raw.items() if k!='exact_degree'}==rb,'pre-rewrite generator replay')
        require({k:v for k,v in body.items() if k!='exact_degree'}==rout and chain==rc,'rewritten generator replay')
        check_chain(raw,body,chain)
        c2=json.loads(json.dumps(construct.build('shared_taps',positive,True,'horner','binary')))
        require({k:v for k,v in cert.items() if k!='exact_degree'}==c2,'degree certificate generator replay')
        dc=construct.degree_certificate(cert)
        require(dc['exact_degree']-20*dc['named_degrees']['D']==1379730,'exact degree from resolved circuit')
        require(degree['exact_degree']==86*7963+328*2115+8*116+264==1379730,'independent degree formula')
        require(dc['unresolved_positive_degree_cancellations']==[],'no unresolved cancellation')
        ops=Counter(x['kind'] for x in body['nodes'] if x['kind'] in ('add','sub','mul'))
        require(sum(ops.values())==body['total_operations']==(478 if positive else 485),'live operation recount')
        ports,fixed=fixed_values(body)
        for p in (1000003,2147483647):
            ps=[x%p for x in ports];ff={k:v%p for k,v in fixed.items()}
            for _ in range(10):
                vs={x:rng.randrange(1 if positive else 0,100) for x in body['variables']}
                ans,D=direct(body,vs,ps,ff,p)
                value,_=evaluate(body,ff,vs,p);old,_=evaluate(raw,ff,vs,p);scaled,_=evaluate(cert,ff,vs,p)
                require(value==old==ans and scaled==pow(D,20,p)*ans%p,'independent modular formula/certificate replay')
                replays+=1
        variants[name]={'degree':1379730,'operations':sum(ops.values()),'counts':dict(ops),'exact_power_rewrite':True,'coefficient_leaves':len(fixed),'certificate_degree':dc['exact_degree']}
    result={'status':'PASS','scope':'Finite source identities, exact majorant and degree identities, full fixed coefficients, exact power rewrite; modular checks are transcription diagnostics only','source':source,'majorant':json.loads(majorant.stdout),'variants':variants,'modular_cases':replays,'source_corruption_rejected':True}
    (R/'VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()

