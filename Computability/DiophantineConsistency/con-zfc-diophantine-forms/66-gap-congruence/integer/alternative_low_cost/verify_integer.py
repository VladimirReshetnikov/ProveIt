"""Independent checker for the round9 ten-integer literal polynomial.

Does not import build_integer.py or upstream code. Finite checks authenticate
data, algebra and exact degree; the unbounded equivalence proof is PROOF.md.
"""
from pathlib import Path
from collections import defaultdict
from itertools import combinations_with_replacement,product
from math import prod
import gzip,hashlib,json,random
ROOT=Path(__file__).resolve().parent
def require(p,msg):
    if not p:raise RuntimeError(msg)
layout=json.loads((ROOT/'data/layout.json').read_text())
body=json.loads((ROOT/'generated/integer10.json').read_text())
source=json.loads((ROOT/'data'/layout.get('source_file','parent_quartic31.json')).read_text())
records=json.loads((ROOT/'generated/source_records.json').read_text())
ports={n:int.from_bytes(gzip.decompress((ROOT/'data'/f'{f}.bin.gz').read_bytes()),'little')for n,f in zip(source['constants'],('beta','K','MC','MF_source'))}
binding=json.loads((ROOT/'data/coefficients_binding.json').read_text())
for r in binding['files']:
    compressed=(ROOT/'data'/(r['name']+'.bin.gz')).read_bytes();raw=gzip.decompress(compressed)
    require(hashlib.sha256(raw).hexdigest()==r['sha256'],'whole tuple raw hash')
    require(hashlib.sha256(compressed).hexdigest()==r['gzip_sha256'],'whole tuple compressed hash')
    require(len(raw)==r['bytes'] and int.from_bytes(raw,'little').bit_length()==r['bit_length'],'whole tuple dimensions')
if 'source_sha256'in layout:
    require(hashlib.sha256((ROOT/'data'/layout['source_file']).read_bytes()).hexdigest()==layout['source_sha256'],'source binding')
fixed={};manifest=json.loads((ROOT/'fixed/MANIFEST.json').read_text())
for row in manifest:
    compressed=(ROOT/'fixed'/(row['name']+'.bin.gz')).read_bytes();raw=gzip.decompress(compressed)
    require(hashlib.sha256(raw).hexdigest()==row['sha256'],'fixed payload hash')
    require(hashlib.sha256(compressed).hexdigest()==row['gzip_sha256'],'gzip hash')
    fixed[row['name']]=row['sign']*int.from_bytes(raw,'little')
require(fixed['radix']==1<<body['base_exponent'],'radix')
require(fixed['threshold']==1<<(16*body['base_exponent']-23),'leadless threshold')
rows=[defaultdict(int,{tuple(t['powers']):t['coefficient']for t in e['terms']})for e in source['equations']]
for dest,src,m in layout.get('source_row_operations',[]):
    for p,c in rows[src-1].items():rows[dest-1][p]+=m*c
for j,sign in enumerate(layout.get('row_orientations',[1]*len(rows))):
    if sign==-1:rows[j]=defaultdict(int,{p:-c for p,c in rows[j].items()})
expected={}
for j,row in enumerate(rows,1):
    groups=defaultdict(dict)
    for p,c in row.items():
        if c:groups[p[:31]][p[31:]]=c*(2 if sum(p[:31])<2 or 2 in p[:31]else 1)
    for alpha,recipe in groups.items():expected[j,alpha]=recipe
require(len(expected)==len(records)==layout.get('record_count',89),'record count')
weights=layout['weights'];targets=dict(zip(layout['order'],layout['targets']));targetset=set(targets.values())
labels=[[(0,)*31],[],[]]
for i in range(31):
    a=[0]*31;a[i]=1;labels[1].append(tuple(a))
for i,j in combinations_with_replacement(range(31),2):
    a=[0]*31;a[i]+=1;a[j]+=1;labels[2].append(tuple(a))
interactions=0;kernels=[defaultdict(int)for _ in range(3)]
for r in records:
    alpha=tuple(r['alpha']);j=r['row'];degree=sum(alpha)
    recipe=expected[j,alpha]
    require(recipe=={tuple(t['powers']):t['coefficient']for t in r['recipe']},'source recipe')
    e=targets[j]-sum(a*w for a,w in zip(alpha,weights));require(e==r['exponent'] and e>=0,'reversed exponent')
    val=sum(c*prod(v**p for v,p in zip(ports.values(),mon))for mon,c in recipe.items())
    ref=r['coefficient'];require(val==(ref['literal']if'literal'in ref else fixed[ref['fixed']]),'fixed recipe')
    kernels[degree][e]+=val
    for beta in labels[degree]:
        hit=e+sum(a*w for a,w in zip(beta,weights))
        require((hit in targetset)==(beta==alpha),'target collision')
        if beta==alpha:require(hit==targets[j],'wrong target')
        interactions+=1
require(interactions==layout.get('exhaustive_interactions',22544),'interaction count')
W=max(weights);H=max(max(k)+i*W for i,k in enumerate(kernels))
require(H==layout['convolution_height'],'height')
require(min(weights)>=1,'positive weights')
require(kernels[2][max(kernels[2])]>0,'positive quadratic leader')
positive_leaders=all(k[max(k)]>0 for k in kernels)
dominant_quadratic=max(kernels[2])+W>max(kernels[1]) and max(kernels[2])+2*W>max(kernels[0])
require(positive_leaders or dominant_quadratic,'source positivity certificate')
M=1<<2134927
require(all(abs(c)<M for k in kernels for c in k.values()),'coefficient bound')
require(fixed['radix']==8192*M,'radix reserve')

def literal(values,mod,heads=False):
    vals=[];degrees=[];lead=[]
    for n in body['nodes']:
        k=n['kind']
        if k=='literal':r=n['value'];de=0;lc=r
        elif k=='fixed':r=fixed[n['name']];de=0;lc=r
        elif k=='variable':r=values[n['name']];de=1;lc=r
        else:
            l,q=n['left'],n['right'];a,b=vals[l],vals[q]
            r=a+b if k=='add'else a-b if k=='sub'else a*b
            de=degrees[l]+degrees[q]if k=='mul'else max(degrees[l],degrees[q])
            lc=lead[l]*lead[q]if k=='mul'else ((lead[l]if degrees[l]==de else 0)+(1 if k=='add'else-1)*(lead[q]if degrees[q]==de else 0))
        vals.append(r%mod);degrees.append(de);lead.append(lc%mod)
    return vals[body['output']],{k:vals[i]for k,i in body['named_nodes'].items()},degrees[body['output']],lead[body['output']]

def direct(v,p):
    def red(x):return x%p
    t,g0,h0,k0,l,w,x,y,z,m=(v[n]for n in body['variables'])
    b=red(6*t+4);g=red(b*g0);h=red(b*h0);k=red(b*(3*k0+2));B=red(fixed['radix']*b*b)
    ell=red(sum(pow(B,a,p)for a in weights));word=red(ell+g)
    Ds=[red(sum((co%p)*pow(B,e,p)for e,co in ks.items()))for ks in kernels]
    coded=red(Ds[2]*word*word+Ds[1]*word+Ds[0]);n0=pow(B,W+1,p);nn=pow(B,W+H+2,p)
    target=red(sum(pow(B,e,p)for e in targets.values()));mask=red(n0-1-(b-1)*ell)
    tc=red(mask+n0*(B-2)*target-2);sc=red(g+n0*(2*coded+target))
    X=red(nn*(sc+tc+1)-sc-1);Y=red(fixed['threshold']*pow(B,H+2*W+9,p)*b);cap=red(b*pow(B,W,p))
    L=red(l*Y);U=red(2*L*X);V=red(4*g*w*Y);ww=red(b*w);a=red(U*(V+1));bb=red(2*X+1);C=red(bb+(a-2)*h)
    ph=red((L*X)*U*V);pn=red(2*ph);K=red(X+1+k*(pn-2));ss=red(2*a-5);tt=red(3*ww*C-2*(ww*ww-1))
    Q=red((ph*ph-1)*K*K+1);delta=red(8*cap**3*g*K*K-g*g*(32*(C-K*L)**2*cap**3+g*g*K*K))
    xi=red(z*x);D=red((a*a-4)*C*C+4);E=red(C*C*D*xi);F=red(4*(a*a-4)*E*E+1)
    G=red(2*(a+2)*(a-2)**2*E*E-1);Om=red(16*E);HH=red(C+(bb-C)*F+Om*F*y);I=red((G*G-1)*HH*HH+1)
    sig=red(xi*pow(ss,5,p));rho=red(tt+ss*y);theta=red((rho**3-rho*ss*ss-ss**3)*(rho*rho+23*ss*ss))
    r=red(b*Q);aa=red(r+(3*delta-1)*(r*z)**2);dd=red(D*F*I);Z=red(sig*m-theta)
    out=red((Z*Z-sig*sig*(aa+dd))**2-4*sig**4*aa*dd)
    return out,dict(b=b,g=g,h=h,k=k,X=X,Y=Y,cap=cap,A=a,C=C,P=pn,K=K,Q=Q,S=ss,T=tt,Delta=delta,D=D,F=F,G=G,H=HH,I=I,Sigma=sig,Theta=theta,guard=aa,lucas=dd,center=Z)

rng=random.Random(934114);replays=0;head_certificates=[]
for prime in (1000000007,1000000009,998244353):
    for _ in range(48):
        values={n:rng.randrange(-11,12)for n in body['variables']};a,named,degree,head=literal(values,prime);b,directnames=direct(values,prime)
        require(a==b,'literal/direct output')
        for k,v in directnames.items():require(v==named[k],'literal/direct '+k)
        replays+=1
    _,_,degree,head=literal({n:1 for n in body['variables']},prime,True)
    require(degree==body['degree_upper_bound'] and head!=0,'exact degree leader')
    head_certificates.append(dict(prime=prime,degree=degree,leading_residue=head))
congruences=0
for t in range(-4,5):
    b=6*t+4
    for _ in range(18):
        v={n:rng.randrange(-4,5)for n in body['variables']};v['t']=t
        mod=abs(24*b*b);_,q,_,_=literal(v,mod)
        require(q['X']%2==1 and q['X']%3==0 and (q['X']+1)%abs(b)==0,'source congruences')
        require(q['Y']%abs(b)==0 and q['K']%abs(3*b)==0,'bridge congruences')
        require((q['Q']-1)%(b*b)==0 and q['Q']%3==1,'Q congruences')
        require(q['D']%abs(4*b)==0,'D congruence')
        require((q['guard']-b)%abs(2*b)==0 and q['lucas']%abs(2*b)==0,'radicand separation')
        congruences+=1
carrychecks=0
for u in range(3,9):
    L=1<<u
    for S in range(0,L,4):
        for T in range(2,L-S,4):
            # T has bit1 set and bit0 clear: clearing exactly bit1 is safe.
            T1=T-2;R=L*(S+T1+1)-S-1
            pop=lambda x:x.bit_count()
            deficit=pop(S)+pop(T1)-pop(S+T1)
            require(pop(R)==u+pop(T)-1-deficit,'carry identity')
            require((S&T)==(S&T1),'fixed zero mask removal')
            require((deficit==0)==((S&T1)==0),'carry zero characterization')
            carrychecks+=1
# Rational-root recovery checked as a formal polynomial identity.
import sympy as sy
q,a,d=sy.symbols('q a d');norm=(q*q-a-d)**2-4*a*d
require(sy.expand((q*q+a-d)**2-4*q*q*a-norm)==0,'two-root recovery identity')
live=set();todo=[body['output']]
while todo:
    i=todo.pop()
    if i in live:continue
    live.add(i);n=body['nodes'][i]
    if 'left'in n:todo.extend((n['left'],n['right']))
require(len(live)==len(body['nodes']),'dead gates')
ops=sum('left'in n for n in body['nodes']);require(ops==body['total_operations'],'count')
result=dict(status='PASS',operations=ops,exact_degree=body['degree_upper_bound'],source_records=len(records),
    isolation_interactions=interactions,actual_tuple_modular_replays=replays,congruence_fixtures=congruences,
    carry_fixtures=carrychecks,degree_certificates=head_certificates,
    boundary='Finite checks authenticate artifacts and identities, not unbounded compiler/Sun/calibration equivalence.')
(ROOT/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
