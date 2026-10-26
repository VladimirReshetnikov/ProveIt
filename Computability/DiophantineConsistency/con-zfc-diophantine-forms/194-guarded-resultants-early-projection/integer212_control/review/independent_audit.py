#!/usr/bin/env python3
"""Independent exact audit; imports no producer or producer polynomial code."""
from pathlib import Path
from collections import defaultdict
import json, hashlib, sys, zipfile

ROOT=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parents[2]/'integer/final'
HERE=Path(__file__).resolve().parent
D=2**20
def require(p,s):
    if not p: raise ValueError(s)
def read(p): return json.loads(p.read_text())
def poly(ts):
    out=defaultdict(int)
    for c,m in ts:
        require(type(c) is int and c!=0,'invalid coefficient')
        require(list(m)==sorted(m) and all(type(i) is int and i>=0 for i in m),'invalid monomial')
        require(tuple(m) not in out,'duplicate term')
        out[tuple(m)]=c
    return dict(out)
def add(*ps):
    out=defaultdict(int)
    for p in ps:
        for m,c in p.items(): out[m]+=c
    return {m:c for m,c in out.items() if c}
def sc(p,k): return {m:k*c for m,c in p.items() if k*c}
def mul(p,q):
    out=defaultdict(int)
    for m,c in p.items():
        for n,d in q.items(): out[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in out.items() if c}
def sq(p): return mul(p,p)
def V(i): return {(i,):1}
def C(c): return {():c} if c else {}
def sub(p,i,q):
    out={}
    for m,c in p.items():
        term=C(c)
        for j in m: term=mul(term,q if j==i else V(j))
        out=add(out,term)
    return out
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def rows(eq): return [poly(r['terms']) for r in eq['residuals']]

source=read(ROOT/'sources/parent213.json'); old=rows(source)
require(digest(ROOT/'inherited/Source173.zip')=='760428ab91a1f39019ebb452d8b347235b5bb1a0935346e23de78b4542e68677','original source173 archive identity')
with zipfile.ZipFile(ROOT/'inherited/Source173.zip') as archive:
    require((ROOT/'sources/parent213.json').read_bytes()==archive.read('ConZFC_CRT_Index_Anchor_215_2026-10-25/stages/affine213/equation.json'),'source173 exact stage')
base=read(ROOT/'base213/equation.json'); actual=rows(base)
require(base.get('inactive_rows')==[130] and base.get('inactive_coordinates')==[184],'inactive horizon staging metadata')
t,F,A,W,w,z,Z=V(0),V(2),add(V(131),C(1)),V(130),V(180),V(181),V(182)
d=add(sc(t,4),C(2)); K=sc(t,D)
# Read no semantic edits from producer certificate: derive the changed rows.
expected=list(old)
expected[91]=add(V(133),sc(W,4),sc(mul(W,V(132)),-8))
expected[92]=add(V(134),sc(mul(W,V(133)),-4),sc(V(133),-1))
expected[96]=add(V(138),sq(d),sc(mul(A,d),-2),C(1))
expected[97]=add(F,C(-1),sc(w,-D),sc(Z,D),sc(mul(d,z),-D),mul(V(138),V(139)))
expected[127]=add(sc(w,2),sc(sq(w),D),sc(sq(z),D),sc(sq(Z),-D))
require(old[126]==add(Z,sc(mul(A,z),-1)),'Az wire')
# All physical unscaled pairs, including the two shifted storage charts.
pairs=[]
indices=[t,add(F,t),add(V(8),C(-1)),V(9),V(10),V(11),V(12),V(4),V(13),V(14),V(1),V(15),sc(V(16),2)]
for i,lo in enumerate([135,144,147,150,153,156,159,162,165,168,171,174,177]):
    X=add(V(lo),V(lo+2),C(1) if lo==171 else {})
    Y=add(V(lo+1),C(-1) if lo==147 else {})
    pairs.append((X,Y,indices[i]))
norm_rows=[95,103,105,107,109,111,113,115,117,119,121,123,125]
raw=add(*(add(sq(add(X,C(-1))),sq(add(Y,sc(k,-1)))) for X,Y,k in pairs),sq(w),sq(add(z,sc(t,-1))),sc(mul(V(131),V(198)),-1))
expected[141]=add(raw,*(sc(old[i],-1) for i in norm_rows))
cap=add(sq(pairs[-1][1]),sc(sq(indices[-1]),-1),C(-1),*(sc(sq(Y),-1) for X,Y,k in pairs[:-1]),sc(sq(z),-1),sc(sq(V(201)),-1),sc(sq(V(202)),-1),sc(V(203),-1),sc(sq(V(203)),-1))
require(old[144]==cap,'literal scaled cap')
# Port list recovered from the actual power blocks, not from atom ledger.
ports=[(d,K,F),(V(3),V(1),V(17)),(V(183),V(1),add(V(94),C(-1)))]
plus_outputs=[95,100,103,106,109,112,116,119,124,127]
plus_pairs=[1,2,3,4,5,6,8,9,11,12]
ports += [(V(94),pairs[i][2],V(o)) for i,o in zip(plus_pairs,plus_outputs)]
ports += [(add(V(94),C(-1)),pairs[i][2],V(o)) for i,o in zip([0,7,10],[96,113,120])]
require(len(ports)==16,'request census')
atoms=[t,add(t,C(1)),add(F,t),V(1),d,V(3),F,V(4),add(V(8),C(-1))]
atoms += [V(i) for i in range(9,16)]
atoms += [sc(V(16),2),V(17),K,add(V(94),C(-1)),V(94),V(183)]
atoms += [V(i) for i in [95,96,100,103,106,109,112,113,116,119,120,124,127]]
require(len(atoms)==35,'atom census')
require(all(p in atoms for port in ports for p in port),'all 48 ports framed')
weights={}
for atom in atoms:
    require(abs(atom.get((),0))<=2,'constant atom budget')
    for m,c in atom.items():
        require(len(m)<=1,'affine atom')
        if m: weights[m[0]]=max(weights.get(m[0],0),abs(c))
expected[128]=add(W,C(-22),*(sc(sq(V(i)),-c) for i,c in weights.items()))
require(expected==actual,'all 152 base residuals independently reconstructed')
changed=[i for i in range(152) if old[i]!=expected[i]]
require(changed==[91,92,96,97,127,128,141],'semantic edit census')
# Direct norm identity after the scaled physical substitution.
physical_norm=add(sq(add(C(1),sc(w,D))),sq(sc(z,D)),sc(sq(sc(Z,D)),-1),C(-1))
require(physical_norm==sc(expected[127],D),'divided norm identity')
certificate=read(ROOT/'semantic_certificate.json')
require([poly(x['terms']) for x in certificate['atoms']]==atoms,'certificate atoms independently match')
require(dict(certificate['frame_weights'])==weights,'weighted frame ledger')
require(certificate['source_sha256']==digest(ROOT/'sources/parent213.json'),'source digest')

# Replay every exact integral operation, and reverse individually/compositely.
ops=read(ROOT/'operations.json'); rr=list(expected)
def apply(rs,op,inverse=False):
    out=list(rs)
    if op['type']=='row':
        i,j,k=op['target'],op['source'],op['multiple']
        require(i!=j and type(k) is int and k!=0,'unit row operation')
        out[i]=add(out[i],sc(out[j],-k if inverse else k))
    else:
        i=op['coordinate']; p=poly(op['image'])
        require(p.get((i,))==1 and all(i not in m for m in p if m!=(i,)),'unit coordinate operation')
        require(all(len(m)<=1 for m in p),'affine coordinate operation')
        if inverse:p=add(sc(p,-1),sc(V(i),2))
        out=[sub(r,i,p) for r in out]
    return out
for op in ops:
    nxt=apply(rr,op)
    require(apply(nxt,op,True)==rr,'individual inverse')
    rr=nxt
for op in reversed(ops): rr=apply(rr,op,True)
require(rr==expected,'composed inverse')
rr=list(expected)
for op in ops: rr=apply(rr,op)
require(all(184 not in m for i,r in enumerate(rr) if i!=130 for m in r),'deleted horizon isolation')
require(rr[130]==add(t,C(-16),sc(sq(V(184)),-4)),'only removed row')
ren=lambda i:i-(i>184)
rr=[{tuple(ren(j) for j in m):c for m,c in r.items()} for i,r in enumerate(rr) if i!=130]
final=read(ROOT/'integer212/equation.json'); require(rows(final)==rr,'all emitted residuals')
require(final['domain']=='unrestricted integers' and final['polynomial']=='sum(square(row) for row in residuals)','final literal domain and polynomial definition')
require(len(final['variables'])==212 and len(rr)==151,'final dimensions')
expansion=add(*(sq(r) for r in rr))
require(expansion==poly(read(ROOT/'integer212/expanded_polynomial.json')['terms']),'every collected quartic coefficient')
metrics={'variables':212,'rows':151,'degree':max(map(len,expansion)),'monomials':len(expansion),'height':max(map(abs,expansion.values())),'row_height':max(abs(c) for r in rr for c in r.values()),'residual_terms':sum(map(len,rr))}
require(metrics==read(ROOT/'integer212/metrics.json'),'all reported metrics')
require(set(j for m in expansion for j in m)==set(range(212)),'every variable live')

# Signed finite regressions supplement, but do not replace, the proof.
def pell_mod(a,n,m):
    p=(1,0);q=(a%m,1);disc=(a*a-1)%m
    def mm(x,y):return ((x[0]*y[0]+disc*x[1]*y[1])%m,(x[0]*y[1]+x[1]*y[0])%m)
    k=abs(n)
    while k:
        if k&1:p=mm(p,q)
        q=mm(q,q);k//=2
    return p[0],p[1] if n>=0 else (-p[1])%m
count=0
for a in [-1048579,-11,-5,-3,3,5,11,1048579]:
    for e in range(2,21):
        h=2**e;m=h*abs(a-1)
        for ell in [-13,-2,-1,0,1,2,13]:
            X,Y=pell_mod(a,h*ell,m)
            require(X%h==1 and Y%h==0,'scaled integrality')
            require(((X-1)//h)%abs(a-1)==0,'scaled X congruence')
            require((Y//h-ell)%abs(a-1)==0,'scaled Y congruence')
            count+=1
receipt={'status':'PASS','scope':'Independent full exact new algebra; original source archive and immediate affine213 bytes authenticated. Full inherited replay is recorded separately. Finite signed tests are regressions, not unbounded proofs.','metrics':metrics,'base_rows_reconstructed':152,'changed_rows':changed,'operations_forward_and_inverse':len(ops),'framed_requests':16,'framed_ports':48,'atoms':35,'framed_coordinates':len(weights),'signed_modular_tests':count,'equation_sha256':digest(ROOT/'integer212/equation.json'),'expansion_sha256':digest(ROOT/'integer212/expanded_polynomial.json'),'optimized_python':bool(sys.flags.optimize)}
print(json.dumps(receipt,sort_keys=True))
