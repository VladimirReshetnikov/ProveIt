#!/usr/bin/env python3
"""Independent finite audit of the direct quadratic 10-integer circuit.

Does not import its generator or execute received source programs. Native
ports are reconstructed from the pinned literal tile file and checked by
their upstream byte hashes. Algebra audits are finite exact checks, not an
end-to-end formal proof of the Pell/compiler/Lucas bridge.
"""
from pathlib import Path
from itertools import product, combinations_with_replacement
from collections import Counter, defaultdict
from math import comb, factorial
import hashlib
import json
import random

ROOT=Path(__file__).resolve().parents[1]
UP=ROOT
BODY=ROOT/'generated/direct10.json'


def require(p,msg):
    if not p: raise ValueError(msg)


def native_ports():
    tiles=json.loads((UP/'coefficients/upstream/wang943_tiles.json').read_text())
    require(len(tiles)==943,'tile count')
    bits,cell,T1,T2=121,8801,4393,5495
    ww=[1 << (10+2*j) for j in range(44)]
    ce={i:1+sum(ww[10*t+j] for t,x in enumerate(tile) for j in range(10)
                 if (x+512)>>j&1)+sum(ww[40:]) for i,tile in enumerate(tiles)}
    ce.update({off+j:ww[10*t+j] for t,off in enumerate((1023,1013,1003,983)) for j in range(10)})
    ce.update({e:ww[40+j] for j,e in enumerate((1095,1096,2195,3296))})
    ce.update({1063:0,1064:0})
    mu=1022+sum(ww)
    dc={e:1 for e in (30,62,1100,2200)}
    for e,c in ce.items():
        for target in (T1,T2):dc[target-e]=dc.get(target-e,0)+c
    targets=[1013+j for j in range(10)]+[1065+j for j in range(10)]+[2195,3296]
    B=1 << (bits*cell)
    DC=sum(c << (bits*e) for e,c in dc.items())
    MC=B-1-sum(1 << (bits*e) for e in ce if e!=1)-(2 << (bits*1063))
    MF0=4+(mu << (bits*T1))+(mu << (bits*T2))
    MF0+=sum(1 << (bits*t) for t in targets)
    MF0+=sum(((1<<119)-1) << (bits*(8792+j)) for j in range(7))
    MF0+=((1<<27)-1) << (bits*8799)
    ports=dict(beta=B-1,K0=DC+(B << (bits*42)),MC=MC,MF=MF0+B-1)
    ledger=[]
    binding=json.loads((UP/'data/upstream_coefficients_binding.json').read_text())
    for row in binding['files']:
        name={'K':'K0','MF_source':'MF'}.get(row['name'],row['name'])
        value=ports[name]
        raw=value.to_bytes((value.bit_length()+7)//8,'little')
        sha=hashlib.sha256(raw).hexdigest()
        require(sha==row['sha256'],'native port hash: '+name)
        require(value.bit_length()==row['bit_length'],'native port bits: '+name)
        ledger.append(dict(name=name,bits=value.bit_length(),sha256=sha))
    return ports,ledger


def shifted_residuals():
    parent_bytes=(UP/'data/parent_quartic31.json').read_bytes()
    parent=json.loads(parent_bytes)
    n=len(parent['variables'])
    require(n==31 and len(parent['equations'])==22,'source dimensions')
    result={}
    for eq in parent['equations']:
        coeff=defaultdict(lambda:defaultdict(int))
        for term in eq['terms']:
            ex=term['powers']
            for alpha in product(*(range(v+1) for v in ex[:n])):
                val=term['coefficient']
                for k,v in zip(alpha,ex):val*=comb(v,k)
                coeff[alpha][tuple(ex[n:])]+=val
        result[eq['number']]={a:{e:c for e,c in rows.items() if c}
                             for a,rows in coeff.items() if any(rows.values())}
    return parent,result,hashlib.sha256(parent_bytes).hexdigest()


def coeff_value(recipe,ports,mod=None):
    total=0
    for ee,cc in recipe.items():
        value=cc
        for a,e in zip(ports,ee):
            value*=pow(a,e,mod) if mod else a**e
        total+=value
    return total%mod if mod else total


def fixed_values(body,ports,p):
    cert=body['source_certificate']
    out={'beta_source':pow(2,cert['coefficient_bound']['source_beta_exponent'],p)}
    pp=[ports[k] for k in body['coefficient_ports']]
    for name,recipe in body['coefficient_recipes'].items():
        out[name]=coeff_value({tuple(r['powers']):r['coefficient'] for r in recipe},pp,p)
    return out


def dag_values(body,fixed,variables,p):
    vals=[]
    for j,node in enumerate(body['nodes']):
        kind=node['kind']
        if kind=='variable':value=variables[node['name']]
        elif kind=='literal':value=node['value']
        elif kind=='fixed':value=fixed[node['name']]
        else:
            require(node['left']<j and node['right']<j,'acyclic DAG')
            a,b=vals[node['left']],vals[node['right']]
            value=a*b if kind=='mul' else a+b if kind=='add' else a-b
        vals.append(value%p)
    return vals


def leading_certificate(body,fixed,p):
    degrees=[];coeffs=[]
    for node in body['nodes']:
        kind=node['kind']
        if kind=='variable':d,c=1,1
        elif kind=='literal':d,c=0,node['value']%p
        elif kind=='fixed':d,c=0,fixed[node['name']]
        else:
            a,b=node['left'],node['right'];da,db=degrees[a],degrees[b]
            if kind=='mul':d,c=da+db,coeffs[a]*coeffs[b]%p
            else:
                d=max(da,db)
                ca=coeffs[a] if da==d else 0
                cb=coeffs[b] if db==d else 0
                c=(ca+cb if kind=='add' else ca-cb)%p
        degrees.append(d);coeffs.append(c)
    d,c=degrees[body['output']],coeffs[body['output']]
    require(d==body['degree_upper_bound'],'degree metadata')
    return dict(modulus=p,degree_upper_bound=d,diagonal_leading_coefficient=c,
                proves_degree_attainment=c!=0)


def finalizer_digest(body):
    stops={body['named_nodes'][name]:name for name in ('b','X','Y','Ccap')}
    hs=[]
    for j,node in enumerate(body['nodes']):
        kind=node['kind']
        if j in stops:text='source:'+stops[j]
        elif kind in ('add','sub','mul'):
            a,b=hs[node['left']],hs[node['right']]
            if kind in ('add','mul'):a,b=sorted((a,b))
            text=kind+':'+a+':'+b
        else:text=json.dumps(node,sort_keys=True)
        hs.append(hashlib.sha256(text.encode()).hexdigest())
    return hs[body['output']]


def source_audit(body,parent,rows,ports):
    cert=body['source_certificate'];n=len(parent['variables'])
    weights=cert['weights'];t=max(weights);order=cert['residual_order']
    require(len(weights)==31 and min(weights)>0,'positive source weights')
    pairs=[a+b for a,b in combinations_with_replacement([0]+weights,2)]
    require(len(pairs)==len(set(pairs))==528,'B2 collision')
    targets=[2*t+j*(2*t+1) for j in range(22)]
    require(targets==cert['target_exponents'],'targets')
    Dsym={}
    bound=0;bits=[ports[k].bit_length() for k in parent['constants']]
    weighted_recipes=set()
    for target,j in zip(targets,order):
        for alpha,recipe in rows[j].items():
            require(sum(alpha)<=2,'quadratic source')
            exponent=target-sum(a*w for a,w in zip(alpha,weights))
            mul=factorial(2-sum(alpha))
            for a in alpha:mul*=factorial(a)
            value={e:c*mul for e,c in recipe.items()}
            require(exponent not in Dsym,'D coefficient collision')
            Dsym[exponent]=(j,alpha,value)
            weighted_recipes.add(tuple(sorted(value.items())))
            b=sum(abs(c) << sum(ei*bi for ei,bi in zip(e,bits)) for e,c in recipe.items())
            bound=max(bound,b)
    for name,recipe in body['coefficient_recipes'].items():
        sig=tuple(sorted((tuple(r['powers']),r['coefficient']) for r in recipe))
        require(sig in weighted_recipes,'unrelated fixed recipe '+name)
    beta_exp=cert['coefficient_bound']['source_beta_exponent']
    require(beta_exp%2==0 and 1<<beta_exp>4*(n+2)**2*bound,'coefficient bound')
    require(Dsym[max(Dsym)]==(5,(0,)*n,{(0,0,0,0):2}),'positive leading channel')
    require(max(Dsym)==targets[-1] and min(Dsym)>=0,'D support')
    # Exhaustively certify no other encoded source monomial can land on any target.
    factor_positions=[(0,(0,)*n)]
    for j,w in enumerate(weights):
        e=[0]*n;e[j]=1;factor_positions.append((w,tuple(e)))
    factor2={}
    for (ea,a),(eb,b) in product(factor_positions,repeat=2):
        ex=tuple(x+y for x,y in zip(a,b));key=ea+eb
        if key in factor2:require(factor2[key][0]==ex,'factor2 collision')
        else:factor2[key]=(ex,0)
        factor2[key]=(ex,factor2[key][1]+1)
    matches=0
    for target,j in zip(targets,order):
        got={}
        for e,(source_j,alpha,recipe) in Dsym.items():
            if target-e not in factor2:continue
            aa,mult=factor2[target-e]
            require(source_j==j and aa==alpha,'cross-target contamination')
            got[alpha]={key:mult*c for key,c in recipe.items()}
            matches+=1
        require(got=={a:{e:2*c for e,c in recipe.items()} for a,recipe in rows[j].items()},'target extraction')
    return Dsym,dict(weight_pairs_checked=528,targets_checked=22,
        source_monomials=len(Dsym),target_matches=matches,
        target_identity='[B^q_j](1+sum n_i B^w_i)^2 D(B) = 2 r_j(n)',
        disjoint_D_blocks=True,source_beta_exponent=beta_exp,
        coefficient_bound_multiplier=4*(n+2)**2,
        signed_convolution_bound='|E_k| <= 2 H (1+sum n_i)^2 < B/2',
        highest_D_coefficient=2,highest_D_exponent=targets[-1])


def check_source_values(body,Dsym,parent,ports):
    rng=random.Random(451029);rows=[];cert=body['source_certificate']
    t=cert['max_weight'];h=cert['convolution_degree'];qs=cert['target_exponents']
    for p in (101,1009,1000003):
        fixed=fixed_values(body,ports,p);pp=[ports[k] for k in parent['constants']]
        for trial in range(18):
            variables={v:rng.randrange(-2*p,2*p) for v in body['variables']}
            if trial<4:variables['f']=(-1,0,1,2)[trial]
            vals=dag_values(body,fixed,variables,p)
            get=lambda name:vals[body['named_nodes'][name]]
            f,g=variables['f'],variables['g'];b=(1+3*f)%p
            B=fixed['beta_source']*b*b%p
            Dc=sum(coeff_value(rec,pp,p)*pow(B,e,p) for e,(_,_,rec) in Dsym.items())%p
            ell=sum(pow(B,w,p) for w in cert['weights'])%p
            N0=pow(B,t+1,p);N1=4*pow(B,h+1,p)%p;N=N0*N1%p
            Mc=(N0-1-(b-1)*ell)%p
            mask=sum(pow(B,q,p) for q in qs)%p
            Tc=(Mc+(B-2)*mask*N0)%p
            Jc=(2*(1+g)**2*Dc+sum(pow(B,i+1,p) for i in range(h+1)))%p
            Sc=(g+Jc*N0)%p;Rc=((Sc+Tc+1)*N+Tc+1)%p
            expected=dict(b=b,base=B,Dcode=Dc,ell=ell,Qmask=mask,N0=N0,N1=N1,N=N,
                          Mcode=Mc,Tcode=Tc,Jcode=Jc,Scode=Sc,Rcode=Rc,
                          X=(N-1)*Rc%p,Y=N*N%p,Ccap=b*pow(B,t,p)%p)
            for name,value in expected.items():require(get(name)==value,'source evaluation '+name)
        rows.append(dict(modulus=p,independent_literal_source_evaluations=18))
    return rows


def main():
    body=json.loads(BODY.read_text());ports,port_ledger=native_ports()
    parent,rs,sha=shifted_residuals()
    require(sha==body['source_certificate']['parent_sha256'],'source hash')
    require(body['variables']==['f','g','h','k','l','w','x','y','z','m'],'variable list')
    operations=Counter(n['kind'] for n in body['nodes'] if n['kind'] in ('add','sub','mul'))
    require(dict(operations)==body['operation_counts'],'operation ledger')
    live=set();todo=[body['output']]
    while todo:
        i=todo.pop()
        if i in live:continue
        live.add(i);node=body['nodes'][i]
        if node['kind'] in ('add','sub','mul'):todo.extend((node['left'],node['right']))
    require(len(live)==len(body['nodes']),'dead gates')
    Dsym,source_report=source_audit(body,parent,rs,ports)
    evaluations=check_source_values(body,Dsym,parent,ports)
    degree=[leading_certificate(body,fixed_values(body,ports,p),p) for p in (101,1009,1000003)]
    require(any(x['proves_degree_attainment'] for x in degree),'no degree attainment witness')
    old=json.loads((UP/'upstream/package31_signed10.json').read_text())
    final_hash=finalizer_digest(body)
    require(final_hash==finalizer_digest(old),'finalizer changed after source replacement')
    result=dict(status='PASS',candidate_sha256=hashlib.sha256(BODY.read_bytes()).hexdigest(),
        variables=10,operation_counts=dict(operations),operations=sum(operations.values()),
        all_nodes_live=True,source_parent_sha256=sha,native_ports=port_ledger,
        source_encoding=source_report,source_evaluations=evaluations,
        degree_certificates=degree,
        finalizer_identity=dict(boundary_names=['b','X','Y','Ccap'],
            shared_structural_sha256=final_hash,
            unchanged_from='31-sun10/signed10/generated/signed10.json'),
        scope='Exact finite identity, coefficient, binding and degree checks; not a proof-assistant certificate of the inherited semantic bridge.')
    output=Path(__file__).with_name('DIRECT10_INDEPENDENT_AUDIT.json')
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
