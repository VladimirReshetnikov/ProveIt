"""Owned independent normalized/balanced composition check; not kernel proof."""
if not __debug__:
    raise RuntimeError('Assertions required; do not run optimized Python.')
import json, re, sys, hashlib, collections
from pathlib import Path
sys.setrecursionlimit(20000)
B=Path(__file__).resolve().parent
J=json.loads((B/'inputs/normalized_certificate.json').read_text())
C=[(bin(int(a))[3:],bin(int(b))[3:],j,k) for a,b,j,k in J['entries']]
T=json.loads((B/'inputs/trees.json').read_text())
source_text=(B/'inputs/KSource215Data.lean').read_text()
def parse_tree(name):
    text=source_text.split('def '+name+' : Tree :=',1)[1].split('\n\n',1)[0]
    toks=re.findall(r'\.\w+|\d+|[()]',text);pos=0
    def go():
        nonlocal pos
        t=toks[pos];pos+=1
        if t=='(':
            v=go();assert toks[pos]==')';pos+=1;return v
        if t=='.node':return ['node',go(),go()]
        if t=='.leaf':return ['leaf',go()]
        if t=='.halt':return ['halt']
        assert t in ('.inc','.decnz','.brk','.cont')
        n=int(toks[pos]);pos+=1;return [t[1:],n]
    v=go();assert pos==len(toks);return v
assert T=={'source':parse_tree('t215'),'reference':parse_tree('tD')}
packed=re.findall(r'\((\d+)%positive,(\d+)%positive,(\d+)%N,(\d+)%N\)',(B/'inputs/NormalizedCert215.v').read_text())
assert [(bin(int(a))[3:][::-1],bin(int(b))[3:][::-1],int(j),int(k)) for a,b,j,k in packed]==C

def build(lo,hi):
    if lo==hi:return ['empty']
    if hi==lo+1:return ['leaf',lo]
    mid=(lo+hi)//2
    return ['node',mid-lo,build(lo,mid),build(mid,hi)]

tree=build(0,len(C))
def flatten(t):
    if t[0]=='empty':return []
    if t[0]=='leaf':return [t[1]]
    a,b=flatten(t[2]),flatten(t[3]);assert t[1]==len(a)
    return a+b
assert flatten(tree)==list(range(len(C)))

visits=[]
def lookup(t,j):
    n=0
    while t[0]=='node':
        n+=1;cut=t[1]
        if j<cut:t=t[2]
        else:j-=cut;t=t[3]
    n+=1
    return (C[t[1]] if t[0]=='leaf' and j==0 else None),n
for j,c in enumerate(C):assert lookup(tree,j)[0]==c
assert lookup(tree,len(C))[0] is None

def walk(t,p):
    q='';i=0
    while t[0]=='node':
        b=p[i] if i<len(p) else '0';q+=b;i+=1;t=t[1+int(b)]
    assert t[0]=='leaf'
    return q,t[1]
def inc(p):
    a=list(p);i=len(a)-1
    while i>=0 and a[i]=='1':a[i]='0';i-=1
    if i>=0:a[i]='1'
    return ''.join(a)
def strip(p,bit,k):
    while p and k:
        k-=p[-1]==bit;p=p[:-1]
    return p
def nextp(q,e,zero=False):
    if e[0]=='inc' or (e[0]=='decnz' and not zero):return inc(q)
    if e[0]=='brk' or (e[0]=='decnz' and zero):return inc(strip(q,'0',e[1] if e[0]=='brk' else 1))
    if e[0]=='cont':return strip(q,'1',e[1])
    raise ValueError(e)
def segment(t,p):
    counts=collections.Counter()
    for _ in range(1000):
        q,e=walk(t,p)
        if e[0] in ('halt','decnz'):return p,counts
        if e[0]=='inc':counts[e[1]]+=1
        p=nextp(q,e)
    raise ValueError('segment fuel exhausted')
queries=[];exact_failures=0
def branch(a,b,j):
    global exact_failures
    pa,ca=segment(T['source'],a);pb,cb=segment(T['reference'],b)
    dest,n=lookup(tree,j);assert dest is not None
    qa,qb,_,_=dest
    assert ca==cb and pa.rstrip('0')==qa.rstrip('0') and pb.rstrip('0')==qb.rstrip('0')
    exact_failures+=(pa!=qa)+(pb!=qb)
    queries.append(j);visits.append(n)
branch('','',0)
halts=0
for a,b,j,k in C:
    qa,ea=walk(T['source'],a);qb,eb=walk(T['reference'],b)
    assert ea==eb
    if ea[0]=='halt':halts+=1;continue
    assert ea[0]=='decnz'
    branch(nextp(qa,ea),nextp(qb,eb),j)
    branch(nextp(qa,ea,True),nextp(qb,eb,True),k)
result={'status':'BALANCED_NORMALIZED_FINITE_CHECK_PASS','entries':len(C),'halts':halts,
 'branches':len(queries),'balanced_node_visits':sum(visits),'max_lookup_visits':max(visits),
 'linear_cons_visits':sum(j+1 for j in queries),'literal_endpoint_comparisons_failing':exact_failures,
 'all_index_lookups_match':True,'scope':'Finite composition checked; proposed Rocq glue not compiled.',
 'inputs':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((B/'inputs').iterdir())}}
(B/'balanced_normalized_tree.json').write_text(json.dumps(tree,separators=(',',':'))+'\n')
(B/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
