#!/usr/bin/env python3
"""Reviewer-owned inert parser. No delivered module import or TM/runtime replay."""
from pathlib import Path
import collections, gzip, hashlib, json
P=Path('/tmp/zfc-intake195/extracted/K216_Partial_Selector_2026-10-20')
B=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/candidate-k217')
OUT=Path(__file__).resolve().parent
pins={}; checks=0

def raw(p):
    b=p.read_bytes(); pins[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}; return b

def obj(p):return json.loads(raw(p))
def need(c,msg):
    global checks
    checks+=1
    if not c:raise AssertionError(msg)

def parse_table(p,halt):
    rows={}; start=None
    for line in raw(p).decode().splitlines():
        if line.startswith('#! start '):start=int(line[9:]);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        need((q,b)not in rows and b in(0,1) and w in(0,1) and d in('L','R'),'row syntax')
        rows[q,b]=(w,d,t)
    states={q for q,b in rows}
    need(set(rows)=={(q,b)for q in states for b in(0,1)},'total binary table')
    need(start==0 and start in states and halt not in states,'start/halt')
    need(all(t in states|{halt}for w,d,t in rows.values()),'successor defined')
    return rows,states

def tree(rows):
    bypath={}
    for p,op,a in rows:
        need(p and set(p)<={'0','1'} and p not in bypath,'source path')
        need((op in('CI','CD')and type(a)is int and 0<=a<9)or(op in('CB','CC')and type(a)is int and a>0)or(op=='CH'and a is None),'source opcode')
        bypath[p]=(op,a)
    nodes={}; spans={}; ords={}; cursor=0
    def walk(p):
        nonlocal cursor
        lo=cursor
        if p in bypath:
            n=bypath[p];ords[p]=cursor;cursor+=1
        else:
            need(any(q.startswith(p+'0')for q in bypath)and any(q.startswith(p+'1')for q in bypath),'full source prefix')
            n=(walk(p+'0'),walk(p+'1'))
        nodes[p]=n;spans[p]=(lo,cursor);return n
    root=walk('')
    need(cursor==len(rows) and list(ords)==[r[0]for r in rows],'exact source order')
    return root,nodes,spans,ords

def cfg(rows,nodes,spans,ords):
    # Route A: ancestors/subtree extents. Route B: literal binary counter/cuts.
    def locate(word):
        p=''
        for bit in word+'0'*(max(map(len,ords))+1):
            p+=bit
            if p in ords:
                need('1'not in word[len(p):],'no stray suffix');return ords[p]
        raise AssertionError('unresolved destination')
    def advance(p):
        return format((int(p or '0',2)+1)%(2**len(p)),f'0{len(p)}b')if p else ''
    def cut(p,bit,k):
        pos=[i for i,b in enumerate(p)if b==bit]
        return p[:pos[-k]]if len(pos)>=k else ''
    def outward(p,bit,k):
        for j in range(len(p)-1,-1,-1):
            if p[j]==bit:
                k-=1
                if k==0:return spans[p[:j]][1]%len(rows)if bit=='0'else spans[p[:j]][0]
        return 0
    g=[]
    for i,(p,op,a)in enumerate(rows):
        if op=='CI': aa=[(i+1)%len(rows)];bb=[locate(advance(p))]
        elif op=='CD':aa=[outward(p,'0',1),(i+1)%len(rows)];bb=[locate(advance(cut(p,'0',1))),locate(advance(p))]
        elif op=='CB':aa=[outward(p,'0',a)];bb=[locate(advance(cut(p,'0',a)))]
        elif op=='CC':aa=[outward(p,'1',a)];bb=[locate(cut(p,'1',a))]
        else:aa=[];bb=[]
        need(aa==bb,'two complete CFG resolutions agree');g.append(aa)
    return g

old=obj(B/'sites217.json');new=obj(P/'source/sites216.json')
need(new==obj(P/'source/sites216.compact.json'),'compact/spaced parsed equality')
a,an,asp,ao=tree(old);b,bn,bsp,bo=tree(new)
need([r[1:]for r in old]==[r[1:]for r in new],'whole primitive word')
need(old[:37]==new[:37],'startup-facing37')
AX='11101001001'
need([r for r in old if not r[0].startswith(AX)]==[r for r in new if not r[0].startswith(AX)],'all nonAX paths')
g0=cfg(old,an,asp,ao);g1=cfg(new,bn,bsp,bo);need(g0==g1,'whole guarded graph')
metrics=dict(dag_nodes=len(set(bn.values())),leaves=len(new),depth=max(map(len,bo)),zero_run=max(len(s)for p in bo for s in p.split('1')),guarded_edges=sum(map(len,g1)),guarded_cases=sum(2 if op=='CD'else 1 for p,op,a in new))
need(metrics==dict(dag_nodes=203,leaves=4751,depth=48,zero_run=6,guarded_edges=6175,guarded_cases=6176),'source census')
oldiv={v:an[k]for k,v in asp.items()};newiv={v:bn[k]for k,v in bsp.items()}
need(newiv[187,228]==oldiv[187,228],'old selector retained')
need(newiv[412,4586]==((oldiv[412,466],newiv[466,4574]),(oldiv[4574,4584],newiv[4584,4586])),'partial-selector four exact legs')
recipe=obj(P/'source/dag_recipe.json');nodes=[];ids={}
def freeze(t):
    z=t if isinstance(t[0],str)else(freeze(t[0]),freeze(t[1]))
    if z not in ids:ids[z]=len(nodes);nodes.append(z)
    return ids[z]
need(freeze(a)==recipe['baseline_root']and len(nodes)==recipe['baseline_nodes'],'recipe baseline')
for n in recipe['new_nodes']:
    need(len(n)==2 and all(type(x)is int and 0<=x<len(nodes)for x in n),'recipe backward edges');nodes.append(tuple(n))
def thaw(i):
    n=nodes[i];return n if isinstance(n[0],str)else(thaw(n[0]),thaw(n[1]))
need(thaw(recipe['candidate_root'])==b,'exact source recipe')
O,Q=parse_table(B/'k217.native.tm',254);T,QS=parse_table(P/'machine/prefold217.native.tm',254);N,R=parse_table(P/'machine/k216.native.tm',254);D,DS=parse_table(P/'machine/k216.tm',216)
tr=obj(P/'source/table_recipe.json');replacements={(q,b):(w,d,t)for q,b,w,d,t in tr['replacement_rows']}
need(len(replacements)==len(tr['replacement_rows'])==20,'20 unique replacement rows')
recon=O|replacements;need(recon==T and Q==QS and len(Q)==217,'prefold reconstruction')
need({k:v for k,v in T.items()if O[k]!=v}==replacements,'all20 are actual changes')
phi=lambda q:164 if q==183 else q
need(R==Q-{183} and len(N)==432,'exact state deletion')
need(T[164,0]==(0,'R',77)and T[183,0]==(0,'R',150)and T[164,1]==T[183,1]==(1,'R',98),'old branch endpoints')
incoming={q:sorted((s,b,w,d)for(s,b),(w,d,t)in T.items()if t==q)for q in(164,183)}
need(incoming=={164:[(143,1,1,'R')],183:[(205,0,0,'R')]},'unique opposite origin markers')
need(N[164,0]==(0,'L',201)and N[201,0]==(0,'R',195)and N[201,1]==(1,'R',196)and N[195,0]==(0,'R',150)and N[196,0]==(0,'R',77),'exact positive three-step selector')
for(q,bit),(w,d,t)in T.items():
    if(q,bit)not in((164,0),(183,0)):need(N[phi(q),bit]==(w,d,phi(t)),'every other row commutes')
mp=obj(P/'machine/canonicalization.json');m={int(k):v for k,v in mp['native_to_canonical'].items()}
need(set(m)==R|{254}and set(m.values())==set(range(217))and len(m)==217,'canonical bijection')
need(m[0]==0 and m[254]==216 and m[84]==84,'mapped initial/halt/dispatch')
need({(m[q],bit):(w,d,m[t])for(q,bit),(w,d,t)in N.items()}==D,'all432 canonical rows')
reach={0};todo=[0]
while todo:
    q=todo.pop()
    for bit in(0,1):
        z=N[q,bit][2]
        if z!=254 and z not in reach:reach.add(z);todo.append(z)
need(reach==R,'all216 graph reachable')
# Delivered evidence is read as data, never treated as our fresh execution.
runtime=obj(P/'evidence/runtime.json');cases=json.loads(gzip.decompress(raw(P/'evidence/runtime_cases.json.gz')))
need(runtime['status']=='UNIVERSAL_MATHEMATICAL_PASS'and runtime['proved_cases']==runtime['expected_cases']==6176,'delivered runtime status/count')
need([(x['site_index'],x['positive'])for x in cases]==[(i,z)for i,row in enumerate(new)for z in((False,True)if row[1]=='CD'else(False,))],'stored ordered exhaustive guards')
for x in cases:need(len(x['duration'])==13 and x['duration'][0]>0 and all(z>=0 for z in x['duration']),'stored positive affine clocks')
need(sum(x['symbolic_steps']for x in cases)==1709992 and min(x['duration'][0]for x in cases)==13,'stored rule/progress census')
lm={int(k):v for k,v in obj(P/'code/inputs/legacy_mapping.json').items()}
for q in R|{254}:lm.setdefault(q,q+1000)
need(len({lm[q]for q in R|{254}})==len(R)+1,'legacy map injective')
rev={lm[q]:q for q in R};cover={tuple(z)for x in cases for z in x['rows']}
for block in runtime['blocks']:
    for e in block['trace']:
        if e[0]in('literal','unary'):cover.add(tuple(e[1][:2]))
need({(rev[q],bit)for q,bit in cover}==set(N),'stored all432 row coverage')
startup=json.loads(gzip.decompress(raw(P/'evidence/startup.json.gz')))
need((startup['steps'],startup['state'],startup['head'],startup['gap'],startup['registers'],startup['spares'])==(313133,84,-5,80,[3,0,0,0,3,0,0,0,0],[1]*130),'stored exact startup target')
need(len(startup['trace'])==313133 and len(startup['one_cells'])==len(set(startup['one_cells']))==277,'stored complete finite startup inventory')
for p in ('code/reconstruct216.py','code/source_equivalence.py','code/audit216.py','code/check_joint_fold.py','code/validate_native.py','code/runtime/symbolic_runtime.py','code/runtime/independent_runtime.py','verify.py','sections/construction.tex','sections/theory.tex','sections/verification.tex','README.md','provenance/ATTRIBUTION.md'):raw(P/p)
for field,p in [('table_sha256',P/'machine/k216.native.tm'),('sites_sha256',P/'source/sites216.json'),('checker_sha256',P/'code/runtime/symbolic_runtime.py'),('helper_sha256',P/'code/runtime/independent_runtime.py')]:need(runtime[field]==pins[str(p)]['sha256'],'delivered runtime identity '+field)
oldsearch=Path('/tmp/k217-helper-exposure');census=obj(oldsearch/'parent-census/census.json')
need(any(x['pair']==[164,183]for x in census['pairs']),'old census included exact pair')
for f in ('census.py','search_spans.py','search_two_legs.py'):raw(oldsearch/f)
raw(OUT/'review_data.py')
result=dict(status='INDEPENDENT_SOURCE_PHYSICAL_STATIC_REVIEW_PASS',findings=[],checks=checks,source_metrics=metrics,table=dict(working_states=216,rows=432,prefold_working_states=217,prefold_replacement_rows=20,keep=164,drop=183,helper=201,incoming=incoming,canonical_dispatch=m[84]),delivered_evidence=dict(runtime_cases=6176,rules=1709992,minimum_affine_duration=13,covered_rows=432,startup_steps=313133,one_cells=277,spares=130,reviewed_as='Stored evidence only; root owns fresh execution'),scope='Own inert source/recipe/CFG/table/record parsing. Full selected supplied code read, none executed or imported. No TM/startup/runtime/proof-assistant replay. Ordinary local positive-block proof independently read; inherited mathematical calibration independently reviewed in peer lane.',authorship='opening_encoder authored this reviewer and earlier bounded helper searches; did not author this submitted216 construction. Prior search scope is disclosed, not claimed exhaustive.',inputs=pins)
(OUT/'review.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:v for k,v in result.items()if k!='inputs'},indent=2))
