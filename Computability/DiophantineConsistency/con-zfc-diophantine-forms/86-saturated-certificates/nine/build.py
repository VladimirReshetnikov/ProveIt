#!/usr/bin/env python3
"""Literal saturated nine-positive polynomials. Python standard library only.

All exponents are fixed. Named registers are polynomial abbreviations.
The two source prefixes are inherited, authenticated mathematical data.
New work: positive Pell saturation and complete-radical majorant.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter, defaultdict
import gzip, hashlib, itertools, json, math
from circuit import DAG

ROOT = Path(__file__).resolve().parent
VARIABLES = ['b','g','h','s','w','C','i','j','n']

def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True)+'\n')

def source_h1868(d):
    c,add,sub,mul,pw,N = d.const,d.plus,d.minus,d.times,d.power,d.save
    v={s:d.var(s) for s in VARIABLES}
    code=json.loads((ROOT/'data/code.json').read_text())
    kernels=json.loads((ROOT/'data/kernels.json').read_text())
    W=116; height=1868; Ecode=1986; kap=2134939
    B=N('B',mul(d.fixed('base_scale'),pw(v['b'],2)))
    req={1,W,W+1,Ecode,1055}
    exponent_groups=[code['weights'],code['targets_by_row']]
    exponent_groups += [[t['exponent'] for t in layer['terms']] for layer in kernels['kernels']]
    for exponents in exponent_groups:
        es=sorted(set(exponents));req.add(es[0]);req.update(y-x for x,y in zip(es,es[1:]))
    todo=req-{0};plan={}
    while len(todo)>1:
        a=max(todo);todo.remove(a);b=max(todo)
        pairs=[(abs(2*x-a),x,a-x) for x in todo if a-x in todo]
        if pairs: _,x,y=min(pairs)
        elif 2*b<a: x,y=(a//2,a//2) if a%2==0 else (a-1,1)
        else: x,y=b,a-b
        plan[a]=(x,y);todo.update((x,y))
    @lru_cache(None)
    def bp(e):
        if e==0:return c(1)
        if e==1:return B
        x,y=plan[e]
        return mul(bp(x),bp(y))
    def horner(pairs):
        merged=defaultdict(list)
        for e,a in pairs:merged[e].append(a)
        terms=sorted((e,add(*aa)) for e,aa in merged.items())
        ex,out=terms.pop()
        while terms:
            ne,z=terms.pop();out=add(mul(out,bp(ex-ne)),z);ex=ne
        return mul(out,bp(ex))
    recipes={};sig={};kn=[]
    for layer in kernels['kernels']:
        pairs=[]
        for t in layer['terms']:
            rec=t['coefficient'];key=json.dumps(rec,sort_keys=True)
            if len(rec)==1 and not any(rec[0]['powers']): node=c(rec[0]['coefficient'])
            else:
                if key not in sig:
                    sig[key]='c%03d'%len(sig);recipes[sig[key]]=rec
                node=d.fixed(sig[key])
            pairs.append((t['exponent'],node))
        kn.append(N('Dcode'+str(layer['degree']),horner(pairs)))
    ell=N('ell',horner([(e,c(1)) for e in code['weights']]))
    targets=N('targets',horner([(e,c(1)) for e in code['targets_by_row']]))
    n0=N('N0',bp(W+1));u=N('Usource',add(ell,v['g']))
    gg=N('Gsource',add(mul(add(mul(kn[2],u),kn[1]),u),kn[0]))
    mask=N('mask',sub(sub(n0,c(1)),mul(sub(v['b'],c(1)),ell)))
    tc=N('Tcode',add(mask,mul(sub(B,c(2)),targets,n0)))
    jc=N('Jcode',add(mul(c(2),gg),targets))
    sc=N('Scode',add(v['g'],mul(jc,n0)))
    L=N('L',mul(c(2),v['b'],bp(Ecode)))
    threshold_exp=(15*kap+1-22)//2
    NN=N('N',mul(d.fixed('threshold_scale'),bp(1055)))
    R1=N('Rplus1',sub(mul(L,add(sc,tc,c(1))),sc))
    R=N('R',sub(R1,c(1)));cap=N('capbase',mul(v['b'],bp(W)))
    N2=pw(NN,2);U=N('U',mul(N2,v['w']));Y=N('Y',mul(N2,v['s']))
    M=N('M',mul(R,Y));MU=N('MU',mul(M,U))
    P=N('P',mul(c(2),M,MU));K=N('K',add(R1,mul(v['h'],sub(P,c(1)))))
    A=N('A',add(M,MU));B1=N('B1',add(mul(c(2),R),c(1)))
    C=N('C',v['C']);W1=N('W1',mul(v['b'],v['w']))
    J=N('J',sub(mul(c(4),A),c(5)))
    Q=N('Q',add(mul(W1,sub(mul(c(3),C),mul(c(2),W1))),c(2)))
    V0=N('V0',mul(P,K));a0=N('a0',add(sub(pw(V0,2),pw(K,2)),c(1)))
    margin=N('margin',sub(mul(pw(K,2),sub(mul(c(4),cap),v['g'])),mul(c(16),cap,pw(sub(C,mul(K,Y)),2))))
    Omega=N('Omega',mul(J,margin))
    E0=N('E0',add(mul(J,add(v['n'],pw(W1,2))),Q))
    return dict(profile='H1868', W=W, height=height, Ecode=Ecode,
                source_degree=7943, threshold_degree=2110, A_degree=16385,
                base_scale_exponent=kap,threshold_scale_exponent=threshold_exp,
                threshold_b_power=0,threshold_B_power=1055,
                block_scale_power_of_two=1,coefficient_recipes=recipes,
                power_plan={str(k):list(v) for k,v in sorted(plan.items())},
                coherent_tuple='whole original31')

def source_compact2082(d):
    old=json.loads((ROOT/'baseline/compact2082/parent.json').read_text())
    env=[]
    for x in old['nodes']:
        k=x['kind']
        if k=='literal':out=d.const(x['value'])
        elif k=='fixed':out=d.fixed(x['name'])
        elif k=='variable':out=d.var(x['name'])
        else:out=d.binary(k,env[x['left']],env[x['right']])
        env.append(out)
    for n,i in old['named_nodes'].items():d.save(n,env[i])
    meta={k:v for k,v in old.items() if k not in ['nodes','output','named_nodes','operation_counts','total_operations','exact_degree','fixed_binding','algebraic_rewrite','refined_majorant']}
    return meta

def evaluate_majorant(d, values, order=(2,3,0,1)):
    poly={tuple(t['powers']):t['coefficient'] for t in json.loads((ROOT/'data/saturated_corrected_P.json').read_text())['terms']}
    c,add,mul,pw=d.const,d.plus,d.times,d.power
    @lru_cache(None)
    def rec(items):
        p=dict(items)
        if not p:return c(0)
        if all(not any(m) for m in p):return c(sum(p.values()))
        common=tuple(min(m[j] for m in p) for j in range(4))
        if any(common):
            rest={tuple(m[j]-common[j] for j in range(4)):v for m,v in p.items()}
            return mul(rec(tuple(sorted(rest.items()))),*(pw(values[j],e) for j,e in enumerate(common) if e))
        j=next(j for j in order if any(m[j] for m in p))
        groups=defaultdict(dict)
        for m,v in p.items():
            mm=list(m);e=mm[j];mm[j]=0;groups[e][tuple(mm)]=v
        ex=max(groups);out=rec(tuple(sorted(groups.pop(ex).items())))
        for ne in sorted(groups,reverse=True):
            out=add(mul(out,pw(values[j],ex-ne)),rec(tuple(sorted(groups[ne].items()))));ex=ne
        return mul(out,pw(values[j],ex))
    return rec(tuple(sorted(poly.items())))

def build(profile,majorant,order=(2,3,0,1)):
    d=DAG();meta=source_h1868(d) if profile=='h1868' else source_compact2082(d)
    c,add,sub,mul,pw,N=d.const,d.plus,d.minus,d.times,d.power,d.save
    reg=d.names.copy();A,C,J=reg['A'],reg['C'],reg['J'];ii=d.var('i')
    am1=N('Am1',sub(pw(A,2),c(1)));C2=N('C2',pw(C,2))
    Dm1=N('Dm1',mul(am1,C2));D=N('D',add(Dm1,c(1)))
    e=N('e',mul(ii,J,C));r=N('r',mul(e,C));CD=N('CD',mul(C,D))
    F=N('F',add(mul(pw(e,2),D,Dm1),c(1)))
    Lam=N('Lambda',sub(add(CD,c(1)),A));G=N('G',add(A,mul(F,Lam)))
    Z=N('Z',add(reg['B1'],mul(sub(d.var('j'),c(1)),C)))
    H=N('H',add(C,mul(F,Z)));GH=N('GH',mul(G,H))
    I=N('I',add(sub(pw(GH,2),pw(H,2)),c(1)))
    raw=N('raw_a1',mul(D,F,I))
    if majorant=='simple':
        T=N('Tmajor',mul(A,e,CD));V1=N('V1',mul(T,GH));a1=N('a1',raw)
    else:
        V1=N('V1',evaluate_majorant(d,(A,C,ii,Z),order))
        scale=N('scale',mul(c(1024),pw(C,5),ii))
        a1=N('a1',mul(pw(scale,2),raw))
    Omega,E0,V0,a0=[reg[n] for n in ['Omega','E0','V0','a0']]
    theta=N('Theta',sub(E0,mul(Omega,add(V0,V1))))
    omega2=pw(Omega,2)
    inner=N('inner',sub(pw(theta,2),mul(omega2,add(a0,a1))))
    out=N('F9',sub(pw(inner,2),mul(c(4),pw(omega2,2),a0,a1)))
    # All names referring to the superseded tail are discarded.
    for name in ['E','k','Tmajor']:
        if name in d.names and (name!='Tmajor' or majorant!='simple'):d.names.pop(name,None)
    nodes,out,names=d.prune(out)
    counts=dict(Counter(n['kind'] for n in nodes if n['kind'] in ('add','sub','mul')))
    degrees=[]
    for node in nodes:
        k=node['kind']
        degrees.append(1 if k=='variable' else 0 if k in ('literal','fixed') else
                       degrees[node['left']]+degrees[node['right']] if k=='mul' else
                       max(degrees[node['left']],degrees[node['right']]))
    a=degrees[names['A']]; rr=degrees[names['R']];W=meta['W']
    degree=(88*a+4*rr+8*W+108) if majorant=='simple' else (59*a+4*rr+8*W+103)
    meta.update(schema='saturated-positive-nine-v1',domain='strictly positive integers',variables=VARIABLES,
                nodes=nodes,output=out,named_nodes=names,total_operations=sum(counts.values()),
                operation_counts=counts,majorant=majorant,majorant_order=list(order),exact_degree=degree,
                named_degree_bounds={k:degrees[v] for k,v in names.items()},
                raw_degree_bound=degrees[out],source_snapshot='c1a102936aca437e9999530a0111e6ddab56dc6d')
    return meta

def materialize_h1868_fixed(body):
    ports=[int.from_bytes(gzip.decompress((ROOT/'data'/f'{n}.bin.gz').read_bytes()),'little') for n in ['beta','K','MC','MF_source']]
    vals={n:sum(t['coefficient']*math.prod(x**e for x,e in zip(ports,t['powers'])) for t in rec)
          for n,rec in body['coefficient_recipes'].items()}
    vals.update(base_scale=2**body['base_scale_exponent'],threshold_scale=2**body['threshold_scale_exponent'])
    records=[]
    for name in sorted({n['name'] for n in body['nodes'] if n['kind']=='fixed'}):
        v=vals[name];raw=abs(v).to_bytes(max(1,(abs(v).bit_length()+7)//8),'little')
        data=gzip.compress(raw,mtime=0);fn='fixed/h1868/'+name+'.bin.gz'
        path=ROOT/fn;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
        records.append(dict(name=name,path=fn,sign=-1 if v<0 else 1,bits=abs(v).bit_length(),
                            raw_sha256=hashlib.sha256(raw).hexdigest(),gzip_sha256=hashlib.sha256(data).hexdigest()))
    write_json(ROOT/'fixed/h1868/BINDING.json',{'format':'unsigned little-endian magnitude with external sign','records':records})

def main():
    results={};choices=[]
    for profile,majorant in [('compact2082','simple'),('h1868','simple'),('h1868','complete')]:
        if majorant=='simple':body=build(profile,majorant)
        else:
            options=[build(profile,majorant,order) for order in itertools.permutations(range(4))]
            body=min(options,key=lambda x:x['total_operations'])
            choices=[dict(order=x['majorant_order'],operations=x['total_operations']) for x in options]
        fn=profile+'_'+majorant+'.json';write_json(ROOT/'equations'/fn,body)
        results[fn]={k:body[k] for k in ['domain','variables','total_operations','operation_counts','exact_degree','majorant','majorant_order']}
        if profile=='h1868':materialize_h1868_fixed(body)
    write_json(ROOT/'certificates/HORNER_CHOICES.json',choices)
    write_json(ROOT/'METRICS.json',results)
    print(json.dumps(results,indent=2))

if __name__=='__main__':main()
