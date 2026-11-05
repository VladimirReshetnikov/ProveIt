#!/usr/bin/env python3
"""Exact rank identity, full-row binding and fixed-leaf accounting; no Lean."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import gzip,hashlib,json,math,random
from collections import Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
PARENT=HERE.parent/'fourteen-normalized-product106'
GRAPH_SHA='61784a1cdc3594174c3e321712322cebdffff20be51ef7f2bc0feb3b8f9498a4'
PARENT_SHA='0485cd1e884b918d766261b1780be117238f0813a965c6d8ae4d805176a5f6e1'
CERT_SHA='16358ce2d453371d2f2d1cad8ab22136ea61ec9ff77200a55264ad56d4a57879'
def need(v,m):
    if not v:raise RuntimeError(m)
def sha(raw):return hashlib.sha256(raw).hexdigest()

# Sparse Laurent ring Z[B^(-1),B,J,G,MC,MF], with B != 0 on specialization.
N=5;zero=(0,)*N
def atom(i):
    e=list(zero);e[i]=1;return {tuple(e):1}
def const(n):return {zero:n} if n else {}
def add(a,b,sign=1):
    z=dict(a)
    for k,v in b.items():
        z[k]=z.get(k,0)+sign*v
        if not z[k]:del z[k]
    return z
def mul(a,b):
    z={}
    for x,u in a.items():
        for y,v in b.items():
            k=tuple(i+j for i,j in zip(x,y));z[k]=z.get(k,0)+u*v
    return {k:v for k,v in z.items() if v}
def live(rows,out):
    edges={r[0]:r[2:] for r in rows};seen=set();leaves=set();todo=[out]
    while todo:
        n=todo.pop()
        if n in edges and n not in seen:seen.add(n);todo.extend(edges[n])
        elif isinstance(n,str) and n not in edges:leaves.add(n)
    return seen,leaves
def eval_graph(g,env,p):
    env={k:v%p for k,v in env.items()}
    for name,op,a,b in g['source']:
        av=a%p if isinstance(a,int) else env[a]
        bv=b%p if isinstance(b,int) else env[b]
        env[name]=((av+bv) if op=='+' else (av-bv) if op=='-' else av*bv)%p
    return env[g['output']]

def main():
    path=HERE/'polynomial.json';raw=path.read_bytes();parentraw=(PARENT/'polynomial.json').read_bytes()
    certbytes=(PARENT/'CERTIFICATE.json').read_bytes()
    need(sha(raw)==GRAPH_SHA and sha(parentraw)==PARENT_SHA and sha(certbytes)==CERT_SHA,'input hash')
    g=json.loads(raw);parent=json.loads(parentraw);cert=json.loads(certbytes)
    need(cert['graph_sha256']==PARENT_SHA and cert['degree']['exact_degree']==106,'degree provenance')
    need(g['derived_rational_leaves']=={'Urank':{'numerator':'MF','denominator':'beta'}},'rational binding')
    need(g['derived_integer_leaves']=={'Wrank':'MC-MF'},'integer binding')
    need(g['witnesses']==parent['witnesses'] and g['fixed_runtime_leaves']==['beta','K0','Urank','Wrank'],'input metadata')
    a,b=parent['source'],g['source'];i=next(k for k,r in enumerate(a) if r[0]=='q2minus1');j=next(k for k,r in enumerate(b) if r[0]=='q2minus1')
    iend=next(k for k,r in enumerate(a) if r[0]=='R');jend=next(k for k,r in enumerate(b) if r[0]=='R')
    need(a[:i]==b[:j] and a[iend+1:]==b[jend+1:],'full prefix/suffix mismatch')
    rank=[['q2minus1','-','q2',1],['shifted_gap','+','gap','Urank'],
          ['rank_product','*','q2minus1','shifted_gap'],['rank_linear','*','J','Wrank'],['R','+','rank_product','rank_linear']]
    need(b[j:jend+1]==rank and len(b)==66,'rank/totals')
    known=set(g['witnesses']+g['fixed_runtime_leaves']);counts=Counter()
    for name,op,x,y in b:
        need(name not in known and op in ('+','-','*'),'bad row')
        need(all(isinstance(t,int) or t in known for t in (x,y)),'non-topological graph')
        known.add(name);counts[op]+=1
    seen,leaves=live(b,g['output'])
    need(len(seen)==66 and leaves==set(g['witnesses']+g['fixed_runtime_leaves']),'dead rows/inputs')
    need(dict(counts)=={'*':37,'+':16,'-':13}==g['operation_counts'],'operation counts')
    B,J,G,MC,MF=(atom(i) for i in range(N));invB={(-1,0,0,0,0):1}
    q=add(mul(B,J),const(1));q2m=add(mul(q,q),const(1),-1)
    u=mul(MF,invB);w=add(MC,MF,-1)
    reduced=add(mul(q2m,add(G,u)),mul(J,w))
    original=add(mul(G,q2m),mul(add(MC,mul(q,MF)),J))
    need(reduced==original,'Laurent rank identity')
    bad=add(mul(q2m,add(G,mul(u,invB))),mul(J,w))
    need(bad!=original,'wrong denominator control')
    ports={}
    for name,entry in parent['coefficient_binding']['ports'].items():
        compressed=(PARENT/'coefficients'/entry['file']).read_bytes()
        need(sha(compressed)==entry['gzip_sha256'],'compressed port '+name)
        rawport=gzip.decompress(compressed)
        need(sha(rawport)==entry['raw_sha256'] and len(rawport)==entry['raw_bytes'],'raw port '+name)
        ports[name]=int.from_bytes(rawport,'big')
    beta,mc,mf=ports['beta'],ports['MC'],ports['MF'];need(beta>0 and beta<mf<2*beta,'current beta/MF bounds')
    divisor=math.gcd(beta,mf);num=mf//divisor;den=beta//divisor;need(den>1,'expected nonintegral rational leaf')
    def record(n):
        raw=abs(n).to_bytes((abs(n).bit_length()+7)//8,'big')
        return {'bits':abs(n).bit_length(),'raw_magnitude_bytes':len(raw),'sha256':sha(raw),'negative':n<0}
    leavesizes={'beta':record(beta),'K0':record(ports['K0']),'Urank_numerator':record(num),
               'Urank_denominator':record(den),'Wrank':record(mc-mf)}
    rng=random.Random(0x10666);prime=1_000_000_007
    need(beta%prime != 0,'sample modulus divides beta')
    for _ in range(100):
        inputs={v:rng.randrange(1,prime) for v in g['witnesses']}
        parentenv=dict(inputs,**ports);newenv=dict(inputs,beta=beta,K0=ports['K0'],
            Urank=mf*pow(beta,-1,prime)%prime,Wrank=mc-mf)
        need(eval_graph(g,newenv,prime)==eval_graph(parent,parentenv,prime),'finite graph control')
    print(json.dumps({'status':'PASS','graph_sha256':GRAPH_SHA,'parent_sha256':PARENT_SHA,
        'parent_degree_certificate_sha256':CERT_SHA,'checker_sha256':sha(Path(__file__).read_bytes()),
        'operations':dict(counts),'live_gates':66,'live_witnesses':len(g['witnesses']),
        'fixed_runtime_leaves':g['fixed_runtime_leaves'],'rational_leaf_nonintegral':True,
        'fixed_leaf_magnitudes':leavesizes,'raw_magnitude_bytes_if_separate':sum(v['raw_magnitude_bytes'] for v in leavesizes.values()),
        'rank_laurent_terms':len(original),'rank_wrong_denominator_control':'rejected','finite_modular_controls':100,
        'degree':106,'degree_scope':'inherited from historical parent certificate after exact polynomial equality',
        'scope':'fixed rational-leaf evaluator; no integer-leaf 66 operation claim, no new Lean or internal derivation'},indent=2,sort_keys=True))
if __name__=='__main__':main()
