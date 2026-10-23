#!/usr/bin/env python3
"""Exact finite certificate for the new direct quadratic encoding.

This checks symbolic target identities and the literal circuit; it does not
assert a new proof-assistant certificate for Sun's/the native compiler theorem.
"""
from pathlib import Path
from itertools import product, combinations_with_replacement
from math import comb,factorial
import gzip, hashlib, json, random, sys, ast
from build_direct10 import construct, weights, VARIABLES, shifted_residuals, source as compile_source
from circuit import evaluate, DAG
from finalizer_tools import quadratic_norm
ROOT=Path(__file__).resolve().parent.parent

def require(ok,msg):
    if not ok:raise ValueError(msg)


def ports():
    old=json.loads((ROOT/'data/native_coefficients_binding.json').read_text())
    active=json.loads((ROOT/'coefficients/COEFFICIENT_BINDING.json').read_text())
    require(active['instance']==old['instance'],'compact native instance mismatch')
    expected={r['name']:(r['bit_length'],r['sha256'],r['file']) for r in old['files']}
    actual={r['port']:(r['bits'],r['sha256'],r['file']) for r in active['materialization']['files']}
    require(actual==expected,'rebuilt complete compact tuple differs from pinned binding')
    out={};rows=[]
    for row in old['files']:
        name=row['name'];path=ROOT/'coefficients'/row['file']
        raw=gzip.decompress(path.read_bytes())
        require(hashlib.sha256(raw).hexdigest()==row['sha256'],'native raw payload mismatch: '+name)
        value=int.from_bytes(raw,'little')
        require(value.bit_length()==row['bit_length'],'native bit length mismatch')
        out[{'K':'K0','MF_source':'MF'}.get(name,name)]=value
        rows.append(dict(port=name,bits=value.bit_length(),sha256=row['sha256'],bytes=len(raw)))
    return out,rows


def coefficient_values(body,ps,modulus=None):
    be=body['source_certificate']['coefficient_bound']['source_beta_exponent']
    vals={'beta_source':pow(2,be,modulus) if modulus else 1<<be}
    order=body['coefficient_ports']
    for name,rows in body['coefficient_recipes'].items():
        total=0
        for row in rows:
            c=row['coefficient']
            for p,e in zip(order,row['powers']):
                c*=pow(ps[p],e,modulus) if modulus else ps[p]**e
                if modulus:c%=modulus
            total+=c
        vals[name]=total%modulus if modulus else total
    return vals


def get_shifted_raw():
    # Independent expansion from raw positive residual term records.
    source=json.loads((ROOT/'data/parent_quartic31.json').read_text())
    n=len(source['variables']);ans={}
    for row in source['equations']:
        rr={}
        for term in row['terms']:
            exp=term['powers'];nonzero=[i for i in range(n) if exp[i]]
            for use in product(*(range(exp[i]+1) for i in nonzero)):
                small=[0]*n;c=term['coefficient']
                for i,k in zip(nonzero,use):small[i]=k;c*=comb(exp[i],k)
                key=tuple(small)+tuple(exp[n:]);rr[key]=rr.get(key,0)+c
        ans[row['number']]={e:c for e,c in rr.items() if c}
    return source,ans


def symbolic_targets(body):
    source,raw=get_shifted_raw();n=len(source['variables']);cfg=body['source_certificate']
    ws=cfg['weights'];t=max(ws);targets=cfg['target_exponents'];rs=cfg['residual_order']
    require(n==31 and len(raw)==22 and len(ws)==31,'wrong parent dimension')
    padded=[0]+ws
    sums=[a+b for a,b in combinations_with_replacement(padded,2)]
    require(len(sums)==528==len(set(sums)),'B2 certificate failed')
    C=[]
    for pair in combinations_with_replacement(range(n+1),2):
        ex=[0]*n
        for i in pair:
            if i:ex[i-1]+=1
        c=1 if pair[0]==pair[1] else 2
        C.append((sum(padded[i] for i in pair),tuple(ex),c))
    Ds={};weighted_record_count=0
    for j,num in enumerate(rs):
        for ex,c in raw[num].items():
            alpha=ex[:n];power=targets[j]-sum(ai*wi for ai,wi in zip(alpha,ws))
            require(power>=0,'negative coding exponent')
            weight=factorial(2-sum(alpha))
            for ai in alpha:weight*=factorial(ai)
            Ds.setdefault(power,{})[ex[n:]]=Ds.setdefault(power,{}).get(ex[n:],0)+c*weight
            weighted_record_count+=1
    Ds={p:{e:c for e,c in rec.items() if c} for p,rec in Ds.items()}
    Ds={p:rec for p,rec in Ds.items() if rec}
    lookup={q:j for j,q in enumerate(targets)};got=[{} for _ in targets];interactions=0
    for p,rec in Ds.items():
        for e,alpha,c in C:
            q=p+e
            if q in lookup:
                j=lookup[q]
                for port_exp,d in rec.items():
                    key=alpha+port_exp;got[j][key]=got[j].get(key,0)+c*d;interactions+=1
    for j,num in enumerate(rs):
        actual={e:c for e,c in got[j].items() if c}
        expected={e:2*c for e,c in raw[num].items()}
        require(actual==expected,'symbolic target identity failed: '+str(num))
    require(Ds[max(Ds)]=={(0,0,0,0):2},'D leading coefficient is not +2')
    # Recreate ordinary bound from actual source coefficients, independent of builder.
    bp=cfg['coefficient_bound']['native_port_bits'];L=0
    for rec in raw.values():
        rr={}
        for ex,c in rec.items():rr.setdefault(ex[:n],{})[ex[n:]]=c
        for co in rr.values():L=max(L,sum(abs(c)<<sum(ei*bi for ei,bi in zip(e,bp)) for e,c in co.items()))
    be=cfg['coefficient_bound']['source_beta_exponent'];threshold=4*33**2*L
    require(be%2==0 and (1<<be)>threshold,'strict source coefficient bound failed')
    require(cfg['coefficient_degree']==max(Ds)==targets[-1],'wrong D degree')
    require(cfg['convolution_degree']==targets[-1]+2*t,'wrong convolution degree')
    return (source,raw,Ds),dict(pair_sums=528,all_pair_sums_distinct=True,
            symbolic_target_identities=22,symbolic_target_interactions=interactions,
            source_coefficient_slots=len(Ds),weighted_raw_records=weighted_record_count,
            max_weight=t,leading_D_coefficient=2,
            source_beta_exponent=be,ordinary_coefficient_upper_bits=L.bit_length(),
            strict_bound_multiplier=4356)


def modular_source_checks(body,ps,sourceinfo):
    source,raw,Ds=sourceinfo;cfg=body['source_certificate'];ws=cfg['weights'];t=max(ws)
    targets=cfg['target_exponents'];hi=cfg['convolution_degree'];be=cfg['coefficient_bound']['source_beta_exponent']
    order=source['constants'];rng=random.Random(20550729);checks=0
    for p in (101,1009,1000003):
        fixed=coefficient_values(body,ps,p)
        for _ in range(12):
            vals={name:rng.randrange(-1000,1001) for name in VARIABLES}
            _,names=evaluate(body,fixed,vals,p)
            f,g=vals['f'],vals['g'];b=(1+3*f)%p;B=pow(2,be,p)*b*b%p
            D=0
            for e,co in Ds.items():
                cc=0
                for pe,c in co.items():
                    term=c
                    for nam,k in zip(order,pe):term=term*pow(ps[nam]%p,k,p)%p
                    cc+=term
                D=(D+cc*pow(B,e,p))%p
            ell=sum(pow(B,w,p) for w in ws)%p
            qmask=sum(pow(B,q,p) for q in targets)%p
            N0=pow(B,t+1,p);N1=4*pow(B,hi+1,p)%p;N=N0*N1%p
            M=(N0-1-(b-1)*ell)%p;T=(M+(B-2)*qmask*N0)%p
            # Direct bounded geometric evaluation, independent of recursive circuit.
            geo=0;term=1
            for k in range(hi+1):geo=(geo+term)%p;term=term*B%p
            J=(2*(1+g)**2*D+B*geo)%p;S=(g+J*N0)%p
            R=((S+T+1)*N+T+1)%p;X=(N-1)*R%p;Y=N*N%p;cap=b*pow(B,t,p)%p
            expected=dict(b=b,base=B,Dcode=D,ell=ell,Qmask=qmask,N0=N0,N1=N1,N=N,Mcode=M,Tcode=T,Jcode=J,Scode=S,Rcode=R,X=X,Y=Y,Ccap=cap)
            for name,v in expected.items():require(names[name]==v,'circuit source mismatch '+name)
            checks+=len(expected)
    return dict(primes=[101,1009,1000003],assignments=36,named_node_checks=checks)


def degree_certificate(body,ps):
    upper=[]
    for n in body['nodes']:
        k=n['kind']
        upper.append(1 if k=='variable' else 0 if k in ('literal','fixed') else
                     upper[n['left']]+upper[n['right']] if k=='mul' else max(upper[n['left']],upper[n['right']]))
    require(upper[body['output']]==body['degree_upper_bound'],'degree mismatch')
    cert=[]
    for p in (101,1009,1000003):
        fixed=coefficient_values(body,ps,p);coeff=[]
        for i,n in enumerate(body['nodes']):
            k=n['kind']
            if k=='variable':v=1
            elif k=='literal':v=n['value']%p
            elif k=='fixed':v=fixed[n['name']]
            else:
                a,b=n['left'],n['right']
                if k=='mul':v=coeff[a]*coeff[b]
                else:v=(coeff[a] if upper[a]==upper[i] else 0)+(-1 if k=='sub' else 1)*(coeff[b] if upper[b]==upper[i] else 0)
            coeff.append(v%p)
        lead=coeff[body['output']];require(lead!=0,'upper degree not attained in diagonal specialization')
        cert.append(dict(prime=p,diagonal='all variables equal T',leading_coefficient=lead,degree=upper[-1]))
    return dict(exact_degree=upper[body['output']],certificates=cert,
                explanation='A nonzero diagonal coefficient at the circuit upper bound proves that exact total degree.')


def add(a,b):
    out=a.copy()
    for e,c in b.items():out[e]=out.get(e,0)+c
    return {e:c for e,c in out.items() if c}
def scale(a,c):return {e:c*v for e,v in a.items() if c*v}
def mul(a,b):
    out={}
    for ea,ca in a.items():
        for eb,cb in b.items():
            e=tuple(a+b for a,b in zip(ea,eb));out[e]=out.get(e,0)+ca*cb
    return {e:c for e,c in out.items() if c}


def norm_identity():
    # Formal product in X,r0,r1,r2. Check that root exponents are even.
    zero=(0,0,0,0);vs=[]
    for i in range(4):e=[0]*4;e[i]=1;vs.append({tuple(e):1})
    expanded={zero:1}
    for signs in product((-1,1),repeat=3):
        term=vs[0]
        for s,v in zip(signs,vs[1:]):term=add(term,scale(v,s))
        expanded=mul(expanded,term)
    require(all(all(e%2==0 for e in ex[1:]) for ex in expanded),'norm is not polynomial in radicands')
    expected={(ex[0],)+tuple(e//2 for e in ex[1:]):c for ex,c in expanded.items()}
    d=DAG();X=d.var('X');aa=[d.var('A'+str(i)) for i in range(3)];out=quadratic_norm(d,X,aa)
    nodes,out,_=d.prune(out);names=['X','A0','A1','A2'];got=[]
    for node in nodes:
        k=node['kind']
        if k=='variable':v=vs[names.index(node['name'])]
        elif k=='literal':v={zero:node['value']} if node['value'] else {}
        else:
            a,b=got[node['left']],got[node['right']]
            v=mul(a,b) if k=='mul' else add(a,scale(b,-1 if k=='sub' else 1))
        got.append(v)
    require(got[out]==expected,'formal 3-root norm mismatch')
    return dict(signed_factors=8,expanded_terms=len(expected),exact_identity=True)


def toy_carry_tests():
    # Two simultaneous quadratic/linear residuals: x*x-x-2 and 1-y.
    # B2 weights {0,1,3}; b=4; B=2^16 comfortably exceeds the bound.
    b=4;B=1<<16;t=3;targets=[6,13];hi=19;N0=B**4;N1=4*B**20
    ell=B+B**3;mask=N0-1-(b-1)*ell;highmask=(B-2)*sum(B**q for q in targets)
    D=2*B**4-B**5-4*B**6+2*B**13-B**10
    geo=sum(B**i for i in range(hi+1));positive=[];count=0
    for x,y in product(range(4),repeat=2):
        g=x*B+y*B**3;J=2*(1+g)**2*D+B*geo
        S=g+J*N0;T=mask+highmask*N0;N=N0*N1
        require(0<=S<N and 0<=T<N,'toy bridge range failed')
        nocarry=(S&T)==0;correct=(x*x-x-2==0 and 1-y==0)
        require(nocarry==correct,'toy simultaneous carry check failed')
        X=(N-1)*((S+T+1)*N+T+1)
        # Kummer at p=2 says v2 central binomial=popcount(X).
        criterion=X.bit_count()>=2*(N.bit_length()-1)
        require(criterion==correct,'toy binomial carry criterion failed')
        if correct:positive.append([x,y])
        count+=1
    # Deliberate invalid digit support is ruled out by the low mask.
    g=B**2
    require(g&mask!=0,'invalid support was not rejected')
    # Deliberate B2 collision is detected exactly.
    bad=[0,1,2]
    ss=[a+b for a,b in combinations_with_replacement(bad,2)]
    require(len(set(ss))<len(ss),'collision negative control failed')
    # If channel 2's mask is omitted, x=2,y=0 becomes a false positive.
    g=2*B;J=2*(1+g)**2*D+B*geo
    S=g+J*N0;T=mask+(B-2)*B**targets[0]*N0
    require(S&T==0,'missing-channel negative control not detected')
    return dict(assignments=count,positive_solutions=positive,
                invalid_support_rejected=True,colliding_weights_rejected=True,
                missing_channel_false_positive_demonstrated=True)


def inherited_finalizer(body):
    # Execute only the unchanged algebraic tail of the pinned package31 builder
    # on the new source block, then require literal DAG identity. The extracted
    # AST consists solely of arithmetic assignments, loops and conditionals.
    text=(ROOT/'upstream/package31_build_signed10.py.txt').read_text()
    parsed=ast.parse(text)
    fn=next(n for n in parsed.body if isinstance(n,ast.FunctionDef) and n.name=='construct')
    def assigned(st,name):
        return isinstance(st,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in st.targets)
    start=next(i for i,st in enumerate(fn.body) if assigned(st,'L'))
    end=next(i for i,st in enumerate(fn.body[start:],start) if isinstance(st,ast.Assign)
             and isinstance(st.targets[0],ast.Tuple) and any(isinstance(t,ast.Name) and t.id=='nodes' for t in st.targets[0].elts))
    fragment=ast.Module(body=fn.body[start:end],type_ignores=[])
    forbidden=(ast.Import,ast.ImportFrom,ast.With,ast.AsyncWith,ast.Try,ast.FunctionDef,ast.ClassDef)
    require(not any(isinstance(node,forbidden) for node in ast.walk(fragment)),'unsafe arithmetic extraction')
    d=DAG();v={name:d.var(name) for name in VARIABLES};obj,rs=shifted_residuals()
    b,X,Y,cap,_,_=compile_source(d,v,obj,rs)
    env=dict(d=d,v=v,b=b,X=X,Y=Y,cap=cap,A=d.plus,M=d.times,S=d.minus,P=d.power,c=d.const,
             merger_degree=5,merged_positivity=True,weight_scheme='structural',adaptive_weights=True,
             quadratic_norm=quadratic_norm)
    exec(compile(fragment,'<pinned-package31-algebra>','exec'),env)
    nodes,out,names=d.prune(env['out'])
    require(nodes==body['nodes'] and out==body['output'] and names==body['named_nodes'],
            'inherited downstream finalizer differs from pinned package31')
    return dict(literal_dag_identical=True,source_sha256=hashlib.sha256(text.encode()).hexdigest(),
                comparison='Pinned package31 algebraic tail with only new source block substituted.')


def main():
    if not __debug__:raise RuntimeError('Run without -O; assertions are certificate checks.')
    body=json.loads((ROOT/'generated/direct10_compact.json').read_text())
    require(body==construct(),'delivered circuit is not the deterministic builder output')
    require(body['variables']==VARIABLES and len(VARIABLES)==10,'wrong unknown domain')
    ps,payloads=ports();sourceinfo,targets=symbolic_targets(body)
    require([ps[n].bit_length() for n in body['coefficient_ports']]==body['source_certificate']['coefficient_bound']['native_port_bits'],'source bits differ from payloads')
    modular=modular_source_checks(body,ps,sourceinfo);degree=degree_certificate(body,ps)
    norm=norm_identity();toy=toy_carry_tests();finalizer=inherited_finalizer(body)
    fixed_values=coefficient_values(body,ps)
    fixed_bit_lengths={n['name']:abs(fixed_values[n['name']]).bit_length() for n in body['nodes'] if n['kind']=='fixed'}
    betaexp=body['source_certificate']['coefficient_bound']['source_beta_exponent']
    betaraw=(1<<betaexp).to_bytes((betaexp+8)//8,'little')
    (ROOT/'data/beta_source.bin.gz').write_bytes(gzip.compress(betaraw,mtime=0))
    instance=dict(instance='direct-quadratic10-on-wang943-checksum67-shared-anchor-length8807-prime581197',
                  native_binding='../coefficients/COEFFICIENT_BINDING.json',
                  beta_source=dict(recipe='2^'+str(betaexp),exponent=betaexp,file='beta_source.bin.gz',
                    raw_sha256=hashlib.sha256(betaraw).hexdigest(),raw_bytes=len(betaraw)),
                  coefficient_recipes='../generated/direct10_compact.json:coefficient_recipes',
                  port_order=body['coefficient_ports'],domain='unrestricted integers',
                  variables=VARIABLES,unknown_parameters=[])
    (ROOT/'data/INSTANCE.json').write_text(json.dumps(instance,indent=2)+'\n')
    old=json.loads((ROOT/'upstream/package31_signed10.json').read_text())
    result=dict(status='PASS',scope='Finite exact arithmetic/symbolic certificate, not end-to-end formalization.',
                source_pinning=dict(parent_sha256=hashlib.sha256((ROOT/'data/parent_quartic31.json').read_bytes()).hexdigest()),
                payloads=payloads,source=targets,modular_source=modular,norm=norm,toy=toy,degree=degree,finalizer=finalizer,
                circuit=dict(variables=10,domain=body['domain'],operations=body['operation_counts'],
                             operation_total=sum(body['operation_counts'].values()),
                             fixed_leaves=sum(n['kind']=='fixed' for n in body['nodes']),
                             fixed_leaf_bit_lengths=fixed_bit_lengths,
                             maximum_fixed_leaf_bit_length=max(fixed_bit_lengths.values()),
                             sha256=hashlib.sha256((ROOT/'generated/direct10_compact.json').read_bytes()).hexdigest()),
                baseline=dict(variables=len(old['variables']),degree=old['degree_upper_bound'],
                              operations=sum(old['operation_counts'].values())))
    (ROOT/'verification/RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
