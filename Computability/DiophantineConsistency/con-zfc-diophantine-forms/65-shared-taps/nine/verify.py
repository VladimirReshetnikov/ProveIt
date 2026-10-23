#!/usr/bin/env python3
"""Independent finite source/circuit audit. All checks remain active under -O.
Unbounded consistency equivalence is proved in PROOF.md and its dependencies.
"""
from pathlib import Path
from collections import defaultdict,Counter
import copy,gzip,hashlib,itertools,json,random
import construct
from circuit import evaluate
from materialize_fixed import values
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

def direct(body,vs,fixed,mod):
    """Formula evaluator independent of the arithmetic DAG generator."""
    v=dict(vs)
    if body['domain']=='positive integers':v['j']-=1
    else:
        for x in v:
            if x!='j':v[x]+=1
    b,g,h,s,w,C,i,j,n=[v[x]%mod for x in ['b','g','h','s','w','C','i','j','n']]
    economy=body['layout'].endswith('economy');suf='_economy' if economy else ''
    layout=json.loads((R/f'data/layout{suf}.json').read_text());ks=json.loads((R/f'data/kernels{suf}.json').read_text())
    ports=[];binding=json.loads((R/'coefficients/COEFFICIENT_BINDING.json').read_text())
    for rec in binding['files']:ports.append(int.from_bytes(gzip.decompress((R/'coefficients'/rec['file']).read_bytes()),'little')%mod)
    B=(fixed['base_scale']%mod)*b*b%mod;W=max(layout['weights']);Hc=layout['convolution_height'];E=Hc+W+2
    def coeff(co):
        ans=0
        for t in co:
            term=t['coefficient']
            for p,e in zip(ports,t['powers']):term=term*pow(p,e,mod)%mod
            ans=(ans+term)%mod
        return ans
    ds=[sum(coeff(t['coefficient'])*pow(B,t['exponent'],mod) for t in k['terms'])%mod for k in ks['kernels']]
    ell=sum(pow(B,x,mod) for x in layout['weights'])%mod;ts=sum(pow(B,x,mod) for x in layout['targets'])%mod
    yy=(ell+g)%mod;gs=((ds[2]*yy+ds[1])*yy+ds[0])%mod;N0=pow(B,W+1,mod)
    mask=(N0-1-(b-1)*ell)%mod;Sc=(g+N0*(2*gs+ts))%mod;Tc=(mask+N0*(B-2)*ts)%mod
    L=(1<<body['block_scale_power_of_two'])*b*pow(B,E,mod)%mod
    RR=(L*(Sc+Tc+1)-Sc-1)%mod
    NN=(fixed['threshold_scale']%mod)*pow(b,body['threshold_b_power'],mod)*pow(B,body['threshold_B_power'],mod)%mod
    U=NN*NN*w%mod;Y=NN*NN*s%mod;M=RR*Y%mod;P=2*M*M*U%mod;K=(RR+1+h*(P-1))%mod;A=M*(U+1)%mod
    B1=(2*RR+1)%mod;W1=b*w%mod;J=(4*A-5)%mod;Q=(3*W1*C-2*(W1*W1-1))%mod
    D=((A*A-1)*C*C+1)%mod;kk=i*J*C%mod;EE=kk*D*C%mod;F=((A*A-1)*EE*EE+1)%mod
    G=(A+F*(C*D+1-A))%mod;HH=(C+F*(B1+j*C))%mod;I=((G*G-1)*HH*HH+1)%mod
    a0=((P*P-1)*K*K+1)%mod;a1=D*F*I%mod;t=b*pow(B,W,mod)%mod
    margin=(K*K*(4*t-g)-16*t*(C-K*Y)**2)%mod;V0=P*K%mod;V1=kk*(8*D*D-4*D-1)*G*HH%mod
    om=J*margin%mod;e0=(J*(n+W1*W1)+Q)%mod;theta=(e0-om*(V0+V1))%mod
    return ((theta*theta-om*om*(a0+64*a1))**2-256*pow(om,4,mod)*a0*a1)%mod

def main():
    result={'status':'PASS','scope':'Finite exact algebra/certificate audit; not an unbounded consistency test','variants':{}}
    rng=random.Random(178324)
    for variant in ['shared_taps','shared_taps_economy']:
        suf='_economy' if variant.endswith('economy') else ''
        layout=json.loads((R/f'data/layout{suf}.json').read_text());ks=json.loads((R/f'data/kernels{suf}.json').read_text());source=audit_source(layout,ks)
        # A mathematical negative control: changing a shared tap must break a target identity.
        corrupt=copy.deepcopy(ks);share=source['shared_taps'][0];term=next(t for t in corrupt['kernels'][share['degree']]['terms'] if t['exponent']==share['exponent']);term['coefficient'][0]['coefficient']+=1
        rejected=False
        try:audit_source(layout,corrupt)
        except ValueError:rejected=True
        require(rejected,'coefficient corruption undetected')
        fixed=values(variant);fb=json.loads((R/'fixed'/variant/'BINDING.json').read_text())
        for rec in fb['records']:
            compressed=(R/'fixed'/variant/rec['file']).read_bytes();raw=gzip.decompress(compressed)
            require(hashlib.sha256(raw).hexdigest()==rec['raw_sha256'] and hashlib.sha256(compressed).hexdigest()==rec['gzip_sha256'],'fixed payload hashes')
            require(rec['sign']*int.from_bytes(raw,'little')==fixed[rec['name']],'fixed payload value')
        tests=0;counts={}
        for positive in [True,False]:
            for cert in [False,True]:
                label=variant+'_'+('positive' if positive else 'natural')+('_certificate' if cert else '')
                body=json.loads((R/'generated'/f'{label}.json').read_text())
                rebuilt=construct.build(variant,positive,cert,'horner','binary' if cert else 'additive')
                require(body==json.loads(json.dumps(rebuilt)),'literal circuit replay')
                ops=Counter(x['kind'] for x in body['nodes'] if x['kind'] in ('add','sub','mul'))
                require(sum(ops.values())==body['total_operations'],'operation recount');counts[label]=sum(ops.values())
                # Exact source-dependent diagonal degree, from the resolved norm identity.
                r=4*body['Ecode']-1;q=2*body['threshold_B_power']+body['threshold_b_power'];W=body['W']
                expected=104*r+400*q+8*W+316
                if cert:
                    dc=json.loads((R/'generated'/f'{label}_degree.json').read_text())
                    require(dc['exact_degree']==expected,'independent exact-degree formula')
                    require(construct.degree_certificate(body)==dc,'full resolved leading-form replay')
                    require(dc['named_degrees']['inner']*2==expected,'inner degree')
                    require(expected>76*r+288*q+8*W+216,'norm subtraction strictly lower')
                for mod in [1000003,2147483647]:
                    for _ in range(6):
                        inputs={x:rng.randrange(1 if positive else 0,37) for x in body['variables']}
                        got,_=evaluate(body,fixed,inputs,mod);require(got==direct(body,inputs,fixed,mod),'independent direct formula replay');tests+=1
        source.update(exact_degree=expected,operation_counts=counts,modular_replays=tests,negative_controls=1,fixed_nonliteral_leaves=len(fixed))
        result['variants'][variant]=source
    (R/'VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
