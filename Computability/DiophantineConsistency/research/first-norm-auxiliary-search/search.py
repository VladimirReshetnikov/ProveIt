#!/usr/bin/env python3
"""Read-only bounded symbolic search; no candidate graph is materialized.
Computes the highest three homogeneous layers with rigorous degree bounds,
and checks one P-1 auxiliary correction plus the finite grouping ledger.
No project Python or incoming code is imported.
"""
import hashlib,json
from collections import Counter
from pathlib import Path
HERE=Path(__file__).resolve().parent
PARENT=HERE.parent/'thirteen-unit-sphere96/polynomial.json'
PIN='48573f58aac3d60f706eb7f52e92f5c061bd74d41ad7e9e9ee3e2ea43dcd9ca1'
def require(b,m):
    if not b:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
raw=PARENT.read_bytes();require(sha(raw)==PIN,'exact full parent')
g=json.loads(raw);syms=g['witnesses']+g['fixed_numerals'];zero=(0,)*len(syms)
def dg(m):return sum(m[:13])
def C(n):return {zero:n} if n else {}
def X(s):
    m=list(zero);m[syms.index(s)]=1;return {tuple(m):1}
def add(a,b,sgn=1):
    z=dict(a)
    for m,c in b.items():z[m]=z.get(m,0)+sgn*c
    return {m:c for m,c in z.items() if c}
def mul(a,b,cut=-1):
    z={}
    for m,c in a.items():
        for n,d in b.items():
            k=tuple(x+y for x,y in zip(m,n))
            if dg(k)>=cut:z[k]=z.get(k,0)+c*d
    return {m:c for m,c in z.items() if c}
def deg(p):return max((dg(m)for m in p),default=-1)
def full(name,source,cache):
    if type(name)is int:return C(name)
    if name not in cache:
        _,o,a,b=source[name];u=full(a,source,cache);v=full(b,source,cache)
        cache[name]=mul(u,v)if o=='*' else add(u,v,1 if o=='+' else -1)
    return cache[name]
def homogeneous(p,d):return {m:c for m,c in p.items()if dg(m)==d}
def rows(p):return [[list(m),c]for m,c in sorted(p.items())]
extra=[['bT','*','qm','T'],['bTG','*','bT','B'],['bTGV','*','bTG','V'],
 ['bTGV2','*','bTGV','bTGV'],['corr0','*','bTGV2','f2'],
 ['corrCoefficient','*',16,'corr0'],['Pminus1','-','N0',1],
 ['correction','*','corrCoefficient','Pminus1'],['correctedU','-','Na','correction']]
source=g['source'][:68]+extra+[r[:]for r in g['source'][68:]]
for r in source:
    if r[0]=='sqU':r[2]=r[3]='correctedU'
require(len(source)==84,'all paid rows')
# Full main norm is small enough to expand; its cancellation is not guessed.
norm=full('N1',{r[0]:r for r in source},{s:X(s)for s in syms})
require(len(norm)==323 and deg(norm)==18,'exact main norm')
# Each pair is (proven degree upper bound, exact terms within two of it).
# Keeping a possibly non-sharp bound after a cancellation is conservative.
J={s:(1 if s in g['witnesses']else 0,X(s))for s in syms}
get=lambda n:(0,C(n))if type(n)is int else J[n]
for n,o,a,b in source:
    da,pa=get(a);db,pb=get(b);bound=da+db if o=='*' else max(da,db)
    p=mul(pa,pb,bound-2)if o=='*'else add(pa,pb,1 if o=='+'else -1)
    p={m:c for m,c in p.items()if dg(m)>=bound-2}
    if n=='N1':bound=18;p={m:c for m,c in norm.items()if dg(m)>=16}
    # Recover exact sharp bound only when a nonzero retained layer is found;
    # do not pretend unknown lower layers are available afterward.
    if n=='correctedU':
        require(bound==48 and deg(p)==46,'two leading layers cancel')
        bound=46;p=homogeneous(p,46)
    if n=='sqU':
        # CorrectedU is known through its exact leader only; the degree92
        # leader is therefore exact even though lower layers are omitted.
        p=homogeneous(p,92)
    J[n]=(bound,p)
require(J['polynomial'][0]==92 and deg(J['polynomial'][1])==92,'exact output92')
leader=homogeneous(J['polynomial'][1],92)
require(leader==mul(J['correctedU'][1],J['correctedU'][1]),'output leader is correctedU squared')
# All variables/ports/producers remain actually reachable in the graph.
S={r[0]:r for r in source};live=set()
def visit(n):
    if type(n)is int or n in live:return
    live.add(n)
    if n in S:visit(S[n][2]);visit(S[n][3])
visit('polynomial');require(live==set(S)|set(syms),'no dead row or leaf')
# Exhaust all set partitions only; this is not a general circuit search.
def parts(xs):
    if not xs:yield [];return
    x,*tail=xs
    for p in parts(tail):
        yield [[x]]+[b[:]for b in p]
        for j in range(len(p)):
            q=[b[:]for b in p];q[j]=[x]+q[j];yield q
ledger={}
for arity,names,degrees,prefix in [(13,['P','Q','U','Z'],[22,18,48,36],68),
                                  (14,['P','Q','U','Z','W'],[22,18,30,34,2],62)]:
    d=dict(zip(names,degrees));best={}
    for p in parts(names):
        k=len(p)
        # Raw squares for13; exactly one W-containing residual for14.
        # Exclude14's single-group square, dominated by the direct product.
        if arity==14 and k==1:continue
        cost=prefix+(len(names)-k)+k+(k-1)+1+(arity==14)
        degree=2*max(sum(d[x]for x in b)for b in p)
        if cost not in best or degree<best[cost]['degree']:best[cost]={'degree':degree,'groups':p}
    ledger[str(arity)]=best
out={'scope':'bounded read-only search, not a new frozen equation certificate or Lean proof',
 'script_sha256':sha(Path(__file__).read_bytes()),'parent_sha256':PIN,'variables':13,
 'operations':dict(Counter(r[1]for r in source)),'paid_total':84,'exact_degree':92,
 'correction_rows':extra,'corrected_U_degree':46,'corrected_U_leader':rows(J['correctedU'][1]),
 'whole_output_leader':rows(leader),'restricted_grouping_ledger':ledger}
print(json.dumps(out,indent=2,sort_keys=True))
