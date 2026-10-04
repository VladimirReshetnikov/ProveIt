#!/usr/bin/env python3
"""Independent inert-DAG audit. Imports/executes no source builder or saved schedule.
Read every residual as a sparse Z-polynomial; derive intended equations from
named positive leaves, the declared arithmetic specification and inert matrices.
"""
import collections
import hashlib
import json
import pathlib
import re
import sys

PACKET = pathlib.Path(sys.argv[1]) if len(sys.argv)>1 else pathlib.Path('/workspace/shared/matrix-chronological-certificate-20261004')
OUT = pathlib.Path(__file__).resolve().parent
DAG_SHA = '95e2563fcfcaecfdc5918ffd6dd7421896350df8969a38f08cbb5f5060d80034'
RECEIPT_SHA = 'f365eb9b62242b395b33766d00a246f0ebcd1a28d867cbcf1173037552b916e0'
def need(ok, msg):
    if not ok: raise ValueError(msg)
def pairs(items):
    obj={}
    for k,v in items:
        need(k not in obj,'duplicate JSON key '+k)
        obj[k]=v
    return obj
def load(path):
    return json.loads(path.read_text(),object_pairs_hook=pairs,parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def gitblob(path):
    data=path.read_bytes()
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
need(sha(PACKET/'evidence/polynomial-dag.json')==DAG_SHA,'DAG SHA256')
need(sha(PACKET/'sources/matrix193_countdown_rows.json')==RECEIPT_SHA,'receipt SHA256')
dag=load(PACKET/'evidence/polynomial-dag.json')
receipt=load(PACKET/'sources/matrix193_countdown_rows.json')
coeff=load(PACKET/'evidence/coefficients.json')
ledger=load(PACKET/'evidence/build-receipt.json')
need(set(dag)=={'body_gate_count','constants','domain','equalities','gates','input','macros','output','ports','schema','witnesses'},'DAG schema fields')
need(dag['schema']=='fixed-positive-integer-polynomial-dag-v1','DAG schema')
need(dag['input']=='x','raw ordinary input')
need(dag['domain']=='x and every witness are strictly positive integers','domain contract')
need(dag['constants']=='Fixed integer literals are free; every binary arithmetic gate is counted','cost contract')
witnesses=dag['witnesses']; gates=dag['gates']; eqs=dag['equalities']; body=dag['body_gate_count']
need(isinstance(witnesses,list) and all(type(w) is str for w in witnesses),'witness list')
need(len(witnesses)==len(set(witnesses)),'unique witness names')
need(type(body) is int and 0<body<len(gates),'body boundary')
vid={'input:x':0}; vid.update({'witness:'+w:i+1 for i,w in enumerate(witnesses)})

# Sparse polynomial arithmetic over Z, with sorted variable-index tuples.
class P:
    __slots__=('d',)
    def __init__(self,d): self.d={m:c for m,c in d.items() if c}
    @staticmethod
    def coerce(o):
        if isinstance(o,P): return o
        need(type(o) is int,'polynomial constant type')
        return P({():o})
    def __add__(a,b):
        b=P.coerce(b); d=a.d.copy()
        for m,c in b.d.items(): d[m]=d.get(m,0)+c
        return P(d)
    __radd__=__add__
    def __neg__(a): return P({m:-c for m,c in a.d.items()})
    def __sub__(a,b): return a+-P.coerce(b)
    def __rsub__(a,b): return P.coerce(b)+-a
    def __mul__(a,b):
        b=P.coerce(b); d={}
        for m,c in a.d.items():
            for n,e in b.d.items():
                k=tuple(sorted(m+n)); d[k]=d.get(k,0)+c*e
        return P(d)
    __rmul__=__mul__
    def __pow__(a,n):
        need(type(n) is int and n>=0,'power index')
        p=P.coerce(1)
        for _ in range(n): p=p*a
        return p
    def __eq__(a,b): return a.d==P.coerce(b).d
    def degree(a): return max((len(m) for m in a.d),default=-1)
    def lead(a):
        deg=a.degree(); return {m:c for m,c in a.d.items() if len(m)==deg}

# Validate all references and topological ordering separately from normalization.
def reftype(ref,limit):
    need(type(ref) is str,'reference type')
    if ref in vid: return ('leaf',vid[ref])
    if ref.startswith('constant:'):
        s=ref[9:]; need(re.fullmatch(r'0|-?[1-9][0-9]*',s) is not None,'canonical constant '+ref)
        return ('constant',int(s))
    if ref.startswith('gate:'):
        s=ref[5:]; need(re.fullmatch(r'0|[1-9][0-9]*',s) is not None,'canonical gate '+ref)
        i=int(s); need(i<limit,'topological gate '+ref)
        return ('gate',i)
    raise ValueError('unknown leaf '+ref)
upper=[]
for i,g in enumerate(gates):
    need(type(g) is list and len(g)==3 and g[0] in ['+','-','*'],'gate shape')
    deg=[]
    for ref in g[1:]:
        typ,value=reftype(ref,i)
        deg.append(0 if typ=='constant' else 1 if typ=='leaf' else upper[value])
    upper.append(sum(deg) if g[0]=='*' else max(deg))
reftype(dag['output'],len(gates))
need(len({e[2] for e in eqs})==len(eqs),'unique residual names')
for e in eqs:
    need(type(e) is list and len(e)==3 and type(e[2]) is str,'residual shape')
    reftype(e[0],body); reftype(e[1],body)
for ref in dag['ports'].values(): reftype(ref,body)

norm=[]
leafpoly={ref:P({(i,):1}) for ref,i in vid.items()}
constpoly={}
def polynomial(ref):
    if ref in leafpoly: return leafpoly[ref]
    if ref.startswith('gate:'): return norm[int(ref[5:])]
    if ref not in constpoly: constpoly[ref]=P.coerce(int(ref[9:]))
    return constpoly[ref]
for op,a,b in gates[:body]:
    aa,bb=polynomial(a),polynomial(b)
    norm.append(aa+bb if op=='+' else aa-bb if op=='-' else aa*bb)
actual={name:polynomial(a)-polynomial(b) for a,b,name in eqs}

# Reconstruct each matrix map by applying actual right-action blocks to basis rows.
tr=receipt['transitions']
need(tr['count']==97 and len(tr['tiles'])==96,'actual choice count')
need(tr['loader']=={'X':'unchanged','Y_matrix':[52891,-29036,94920,-52109],'counter_change':-1},'loader interface')
need(tr['tile_counter_guard']=='n=next_n=0','tile guards')
need(receipt['initial_state']=={'X':[35426321,-19628667],'Y':[1,0],'instructions':[],'n':'ordinary_x','operations':0},'actual initializer')
initial=[35426321,-19628667,1,0]
ids=[t['tile_id'] for t in tr['tiles']]
need(len(set(ids))==96 and all(type(i) is int for i in ids),'retained tile IDs')
def det(m): return m[0]*m[3]-m[1]*m[2]
def reconstruct_map(K,G):
    need(type(K) is list and type(G) is list and len(K)==len(G)==4,'matrix dimensions')
    need(all(type(v) is int for v in K+G),'matrix integer entries')
    need(det(K)==det(G)==1,'SL2 matrices')
    images=[]
    for j in range(4):
        z=[int(j==k) for k in range(4)]
        images.append([z[0]*K[0]+z[1]*K[2],z[0]*K[1]+z[1]*K[3],z[2]*G[0]+z[3]*G[2],z[2]*G[1]+z[3]*G[3]])
    return [[images[s][r] for s in range(4)] for r in range(4)]
maps=[reconstruct_map([1,0,0,1],tr['loader']['Y_matrix'])]
for t in tr['tiles']:
    need(det(t['H'])==1,'H determinant')
    maps.append(reconstruct_map(t['K'],t['G']))
offsets=[[1-sum(row) for row in A] for A in maps]
threshold=max([128]+[2+sum(abs(a) for a in row)+abs(1-sum(row)) for A in maps for row in A])
C=1
while C<threshold: C*=2
expected_coeff={'initial':initial,'maps':maps,'offsets':offsets,'tile_ids':ids,'radix_factor':C,'radix_threshold':threshold,'source_receipt_sha256':RECEIPT_SHA,'convention':'A[output][input] represents the actual row-vector right action'}
need(coeff==expected_coeff,'entire coefficient manifest')
need(C==2**104 and threshold==18510406623962009412894903228521,'independent numerical C')

# Reconstruct allowed leaf set and macro interfaces without trusting metadata.
used=set(); expected={}; expectedmac={}; expectedports={}
def w(name):
    need('witness:'+name in vid,'missing witness '+name)
    used.add(name)
    return leafpoly['witness:'+name]
def n(name): return w(name+'.Plus')-1
def eq(name,left,right):
    need(name not in expected,'duplicate intended residual '+name)
    expected[name]=P.coerce(left)-P.coerce(right)
def power(name,b,e):
    b,e=P.coerce(b),P.coerce(e)
    out=w(name+'.out'); a=w(name+'.aMinus1')+1; beta=w(name+'.betaMinus1')+1
    ww=w(name+'.w'); M=w(name+'.modulus'); g=w(name+'.g')
    x=w(name+'.x'); y=w(name+'.y'); u=w(name+'.u'); v=w(name+'.v'); s=w(name+'.s'); t=w(name+'.t')
    qb=w(name+'.qb'); qv=w(name+'.qv'); strict=w(name+'.strict')
    dwb=n(name+'.dwb'); dwk=n(name+'.dwk'); dyk=n(name+'.dyk')
    al1=n(name+'.alpha1'); al2=n(name+'.alpha2'); si1=n(name+'.sigma1'); si2=n(name+'.sigma2')
    ta1=n(name+'.tau1'); ta2=n(name+'.tau2'); rh1=n(name+'.rho1'); rh2=n(name+'.rho2')
    k=e+1; m=b*out
    formula=[(x**2,1+(a**2-1)*y**2),(u**2,1+(a**2-1)*v**2),(s**2,1+(beta**2-1)*t**2),
             (beta,1+4*y*qb),(beta+u*al1,a+u*al2),(v,y**2*qv),
             (s+u*si1,x+u*si2),(t+4*y*ta1,k+4*y*ta2),(y,k+dyk),(ww,b+dwb),(ww,k+dwk),
             (M,m+strict),(a**2,1+((ww+1)**2-1)*(ww*g)**2),(2*a*b,M+b**2+1),
             (x+M*rh1,y*(a-b)+m+M*rh2)]
    for j,(lhs,rhs) in enumerate(formula,1): eq(name+'.eq'+str(j),lhs,rhs)
    expectedmac[name]={'kind':'power','base':b,'exponent':e,'out':out}
    return out
def subset(name,mask,value):
    mask,value=P.coerce(mask),P.coerce(value)
    R=power(name+'.radix',2,mask+1)
    Y=power(name+'.slot',R,value)
    Z=power(name+'.binomial',R+1,mask)
    q=n(name+'.quotient'); half=n(name+'.half'); r=n(name+'.remainder')
    dg=w(name+'.digit_gap'); rg=w(name+'.remainder_gap')
    eq(name+'.extract',Z,(q*R+2*half+1)*Y+r)
    eq(name+'.digit_bound',2*half+1+dg,R)
    eq(name+'.remainder_bound',r+rg,Y)
    expectedmac[name]={'kind':'subset','mask':mask,'value':value}
x=leafpoly['input:x']; h=w('time.h'); ell=w('bounds.ell')
H=power('bounds.offset',2,ell); D=2*H; b=C*D
W=power('time.end_power',b,h); R=n('time.repetition')
eq('bounds.initial',H,35426321+w('bounds.initial_gap'))
eq('bounds.input',x+w('bounds.input_gap'),D)
eq('time.repetition_equation',(b-1)*R+1,W)
E=[n('choice.'+str(i)) for i in range(97)]
for i in range(97): subset('choice.mask.'+str(i),R,E[i])
eq('choice.one_hot',sum(E),R)
Q=[[n('slice.'+str(i)+'.'+str(s)) for s in range(4)] for i in range(97)]
for i in range(97):
    for s in range(4): subset('slice.mask.'+str(i)+'.'+str(s),(D-1)*E[i],Q[i][s])
U=[sum(Q[i][s] for i in range(97)) for s in range(4)]
V=[n('post.'+str(s)) for s in range(5)]
for s in range(5): subset('post.mask.'+str(s),(D-1)*R,V[s])
N=n('counter.pre'); subset('counter.loader_mask',(D-1)*E[0],N)
f=[n('final.'+str(s)) for s in range(4)]
for s in range(4):
    eq('final.bound.'+str(s),f[s]+w('final.gap.'+str(s)),D)
    eq('chronology.row.'+str(s),b*V[s]+H+initial[s],U[s]+W*f[s])
eq('chronology.counter',b*V[4]+x,N)
eq('endpoint.0',f[0],f[2]); eq('endpoint.1',f[1],f[3])
for r in range(4):
    # Direct signed affine expression, independent of author's sign-split schedule.
    rhs=sum(maps[i][r][s]*Q[i][s] for i in range(97) for s in range(4))
    rhs=rhs+H*sum(offsets[i][r]*E[i] for i in range(97))
    eq('transition.row.'+str(r),V[r],rhs)
eq('transition.counter',N,V[4]+E[0])
expectedports={'duration':h,'offset_exponent':ell,'offset':H,'digit_limit':D,'radix':b,'end_power':W,'repetition':R,'counter_pre':N,'counter_post':V[4]}
for i in range(97):
    expectedports['selector.'+str(i)]=E[i]
    for s in range(4): expectedports['slice.'+str(i)+'.'+str(s)]=Q[i][s]
for s in range(4):
    expectedports['pre.'+str(s)]=U[s]; expectedports['post.'+str(s)]=V[s]; expectedports['final.'+str(s)]=f[s]
need(set(witnesses)==used,'exact witness set')
need(set(actual)==set(expected),'exact residual names')
for name,p in expected.items(): need(actual[name]==p,'residual polynomial mismatch '+name)
need(set(dag['ports'])==set(expectedports),'exact port set')
for name,p in expectedports.items(): need(polynomial(dag['ports'][name])==p,'port polynomial mismatch '+name)
macs={m['name']:m for m in dag['macros']}
need(len(macs)==len(dag['macros']) and set(macs)==set(expectedmac),'exact macro set')
for name,m in expectedmac.items():
    need(set(macs[name])==set(m)|{'name'},'macro field set '+name)
    need(macs[name]['kind']==m['kind'],'macro kind '+name)
    for key,value in m.items():
        if key!='kind': need(polynomial(macs[name][key])==value,'macro argument '+name+'.'+key)

# Sum-of-squares structure: every residual exactly once; no omitted, weighted or aliased term.
need(len(gates)-body==3*len(eqs)-1,'SOS tail length')
squares=[]
for j,(a,b,name) in enumerate(eqs):
    k=body+2*j
    need(gates[k]==['-',a,b],'SOS residual '+name)
    need(gates[k+1]==['*','gate:'+str(k),'gate:'+str(k)],'SOS square '+name)
    squares.append('gate:'+str(k+1))
last=squares[0]
for j,s in enumerate(squares[1:]):
    k=body+2*len(eqs)+j
    need(gates[k]==['+',last,s],'SOS sum chain')
    last='gate:'+str(k)
need(dag['output']==last,'output is entire SOS')

# Independent liveness traversal.
seen=set(); pending=[dag['output']]
while pending:
    ref=pending.pop()
    if ref in seen: continue
    seen.add(ref)
    if ref.startswith('gate:'): pending.extend(gates[int(ref[5:])][1:])
need(all('gate:'+str(i) in seen for i in range(len(gates))),'dead gate')
need(all('witness:'+name in seen for name in witnesses),'dead witness')
need('input:x' in seen,'dead raw input')

# Exact residual degrees, plus an explicit degree-12 noncancellation monomial.
degrees=collections.Counter(p.degree() for p in actual.values())
need(max(degrees)==6,'residual exact degree bound')
ww=vid['witness:bounds.offset.w']; gg=vid['witness:bounds.offset.g']
mono6=tuple(sorted([ww]*4+[gg]*2)); mono12=tuple(sorted([ww]*8+[gg]*4))
need(actual['bounds.offset.eq13'].d[mono6]==-1,'attaining monomial')
# All squared degree-six homogeneous parts have this one degree-12 coefficient in total.
coef12=0
for p in actual.values():
    lead={m:c for m,c in p.d.items() if len(m)==6}
    target=collections.Counter(mono12)
    for m,c in lead.items():
        left=target-collections.Counter(m)
        if len(m)+sum(left.values())!=12 or any(collections.Counter(m)[v]>target[v] for v in m): continue
        other=tuple(sorted(left.elements()))
        coef12+=c*lead.get(other,0)
need(coef12==1,'exact degree-12 monomial coefficient')
need(upper[int(dag['output'][5:])]==12,'syntactic degree bound')
counts=lambda gg:dict(sorted(collections.Counter(g[0] for g in gg).items()))
result={'status':'PASS','dag_sha256':DAG_SHA,'source_receipt_sha256':RECEIPT_SHA,
        'builder_sha256':sha(PACKET/'build_certificate.py'),
        'positive_witnesses':len(witnesses),'equalities':len(eqs),'gates':len(gates),
        'body_gate_count':body,'body_counts':counts(gates[:body]),'sos_counts':counts(gates[body:]),'full_counts':counts(gates),
        'macros':dict(collections.Counter(m['kind'] for m in dag['macros'])),'ports':len(dag['ports']),
        'exact_residual_degrees':dict(sorted(degrees.items())),'degree_upper_bound':12,'exact_degree':12,
        'degree_12_attaining_monomial':'bounds.offset.w^8 * bounds.offset.g^4','degree_12_coefficient':coef12,
        'radix_factor':C,'radix_threshold':threshold,'matrix_maps_checked':len(maps),
        'coefficient_entries_checked':97*4*4,'dead_gates':0,'dead_witnesses':0,
        'all_residuals_exactly_reconstructed':True,'all_macro_arguments_exactly_reconstructed':True,
        'all_ports_exactly_reconstructed':True,'raw_input_unshifted':True,
        'builder_or_upstream_program_executed':False,'saved_accepting_schedules_executed':False}
for k in ['positive_witnesses','equalities','gates','body_counts','sos_counts','full_counts','macros','ports','degree_upper_bound','radix_factor','radix_threshold','dead_gates','dead_witnesses','dag_sha256','builder_sha256','source_receipt_sha256']:
    need(result[k]==ledger[k],'claimed ledger mismatch '+k)
for filename in ['matrix193_synchronized_rows.md','matrix195_counted_suffix.md']:
    need(sha(PACKET/'sources'/filename)==receipt['pins'][filename],'upstream receipt document pin '+filename)
blobpins={'matrix193_countdown_rows.md':'cd83d69f27946448df07b0409e44c81ac0559600','matrix195_counted_suffix.md':'5b0af4b4c3a6c61f5eee75beed2c1d586b86c519','matrix193_countdown_rows.json':'d8cdf1509237575bfce3b9c96faf3c883c998412'}
result['document_git_blob_pins']={}
for filename,expected_blob in blobpins.items():
    actual_blob=gitblob(PACKET/'sources'/filename)
    need(actual_blob==expected_blob,'Git blob pin '+filename)
    result['document_git_blob_pins'][filename]=actual_blob
(OUT/'source-audit-receipt.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
print(json.dumps(result,sort_keys=True,indent=2))
