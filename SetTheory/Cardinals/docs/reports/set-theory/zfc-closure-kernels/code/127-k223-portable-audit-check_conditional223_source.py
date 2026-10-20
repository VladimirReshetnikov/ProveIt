#!/usr/bin/env python3
"""Independent exact binding for conditional-K 223 source. No project imports."""
from pathlib import Path
from functools import cache
from collections import defaultdict,Counter
import hashlib,json
A=Path(__file__).resolve().parent;P=A.parent/'inputs';C=A.parent/'results'
def need(x,m):
 if not x:raise ValueError(m)
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_bytes())
def leaf(n):return type(n[0]) is str
def tree(sites):
 d={p:(op,arg)for p,op,arg in sites};need(len(d)==len(sites),'duplicate sites')
 pre={p[:i] for p in d for i in range(len(p))};need(not(set(d)&pre),'prefix leaf');need(all(p+b in d or p+b in pre for p in pre for b in '01'),'binary completeness')
 def go(p):return d[p]if p in d else(go(p+'0'),go(p+'1'))
 return go('')
def sites(n,p=''):return [(p,*n)]if leaf(n)else sites(n[0],p+'0')+sites(n[1],p+'1')
@cache
def flat(n):return (n,)if leaf(n)else flat(n[0])+flat(n[1])
def graph(s):
 d={p:(op,k)for p,op,k in s};iv={}
 def walk(p,i):
  j=i+1 if p in d else walk(p+'1',walk(p+'0',i));iv[p]=i,j;return j
 N=walk('',0)
 def jump(p,b,k):
  for i in range(len(p)-1,-1,-1):
   if p[i]==b:
    k-=1
    if not k:return iv[p[:i]][1 if b=='0'else 0]%N
  return 0
 out=[]
 for j,(p,op,k)in enumerate(s):
  need(op in ('CH','CI','CD','CB','CC')and ((op=='CH'and k is None)or(type(k)is int and k>=0)),'invalid primitive')
  dest=[]if op=='CH'else [(j+1)%N]if op=='CI'else [(j+1)%N,jump(p,'0',1)]if op=='CD'else [jump(p,'0'if op=='CB'else'1',k)]
  out.append([op,k,dest])
 return out
oldsites=read(P/'baseline_sites.json');old=tree(oldsites);need(sha((P/'baseline_sites.json').read_bytes())=='309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878','baseline source identity')
T={}
for line in (P/'parent225.k.tm').read_text().splitlines():
 if line and not line.startswith('#'):
  q,b,w,m,z=line.split();T[int(q),int(b)]=int(w),1 if m=='R'else-1,int(z)
entries=defaultdict(set)
def decode(n,p,q):
 if leaf(n):return
 entries[q].add(n)
 for b in (0,1):
  if leaf(n[b]):continue
  cells={i:int(v)for i,v in enumerate(p+str(b))};cells[-1]=1;original=cells.copy();h=len(p);state=q
  for step in range(100):
   if h==len(p)+1:break
   need(h in cells,'prefix escape');w,m,state=T[state,cells[h]];cells[h]=w;h+=m
  need(h==len(p)+1 and cells==original,'decoder exact endpoint');decode(n[b],p+str(b),state)
decode(old,'',84)
def sole(q):need(len(entries[q])==1,'ambiguous source entry');return next(iter(entries[q]))
mac={166:sole(98),121:sole(12),168:sole(166),119:sole(90),180:sole(86),218:sole(184),177:sole(184)[0]};mac[181]=(mac[119],('CI',1));mac[182]=(mac[180],('CI',1))
I=lambda x,y:('I',x,y);Q=lambda x,y:('Q',x,y);R=lambda x,y:('R',x,y);E=lambda x,y:('E',x,y);N=lambda x:I(x,1)
# Independently spell the unchanged support/closure body from K's definition.
# XA is the already fused expansion of Ex_x(A AND B).
XA=lambda x,a,b:N(Q(x,I(a,N(b))))
m='c';a='a';b='b';k='c';r=R(b,k);sub=Q(k,I(R(k,a),R(k,b)));w=Q(b,I(m,XA(b,m,r)));u=Q(a,I(sub,w));H=Q(b,I(r,XA(a,m,u)))
oldcore=XA(k,I(m,r),H);newcore=I(m,XA(k,r,H))
def emit(f):
 if type(f)is str:return[{'a':166,'b':121,'c':168}[f]]
 if f==1:return[177]
 if f[0]=='I'and f[2]==1:return emit(f[1])+[218]
 return emit(f[1])+emit(f[2])+[{'I':119,'Q':180,'R':181,'E':182}[f[0]]]
def stack(word):
 s=[]
 for x in word:
  if x in (166,121,168,177):s.append({166:a,121:b,168:k,177:1}[x])
  elif x==218:s[-1]=N(s[-1])
  else:
   y=s.pop();x0=s.pop();s.append(({119:I,180:Q,181:R,182:E}[x])(x0,y))
 need(len(s)==1,'emitter stack balance');return s[0]
def tup(v):return tuple(map(tup,v))if isinstance(v,list)else v
contract=read(P/'emitter_contract.json');oldword=contract['canonical_word'];need(oldword[:47]==emit(oldcore),'old core contract');need(stack(oldword)==tup(contract['canonical_expression']),'baseline exact AST');newword=emit(newcore)+oldword[47:];actual=stack(newword)
VR=I(R(a,b),Q(k,R(a,b)));VE=I(E(a,b),Q(R(a,b),E(a,b)));bundle=N(I(newcore,I(VR,N(VE))));need(actual==bundle,'independent new bundle')
part,tail=sole(227),sole(224)
def seq(xs):
 n=xs[0]
 for t in xs[1:]:n=n,t
 return n
oldpart=seq([mac[x]for x in emit(oldcore)[1:]+[166,121,181]]+[tail]);need(flat(oldpart)==flat(part),'old replacement interval exact leaves')
def replace(n,from_,to):
 if n==from_:return to
 return n if leaf(n)else tuple(replace(v,from_,to)for v in n)
need(graph(sites(replace(old,part,oldpart)))==graph(oldsites),'baseline reassociation CFG')
newpart=seq([mac[x]for x in emit(newcore)[1:]+[166,121,181]]+[tail]);reference=replace(old,part,newpart);candidate_sites=read(C/'sites.json');candidate=tree(candidate_sites)
need(flat(reference)==flat(candidate),'new instruction sequence differs');G=graph(candidate_sites);need(G==graph(sites(reference)),'new whole-source guarded CFG differs')
# Exact surrounding source context: the replacement occurs once and leaves every
# other leaf, all gate/reset/parser instructions and eight logical rows intact.
occ=[]
def find(n,p=''):
 if n==part:occ.append(p)
 if not leaf(n):find(n[0],p+'0');find(n[1],p+'1')
find(old);need(len(occ)==1,'multiple replacement sites')
allnodes=set()
def census(n):
 allnodes.add(n)
 if not leaf(n):census(n[0]);census(n[1])
census(candidate)
certpath=A.parent/'theory/conditional_fusion_certificate.json';cert=read(certpath)
need(cert.get('core')=='conditional'and cert.get('equality_binder')=='kappa','Wrong fusion certificate family')
def label(x):return k if x=='k'else R(a,b)if x=='kappa'else x
@cache
def certform(j):
 t=cert['terms'][j];tag=t[0]
 if tag=='F':return 1
 if tag=='meta':need(t==['meta','m'],'Unexpected matrix parameter');return m
 if tag=='I':return I(certform(t[1]),certform(t[2]))
 if tag=='Q':return Q(label(t[1]),certform(t[2]))
 need(tag in ('Rel','Eq'),'Unexpected fusion atom');return (R if tag=='Rel'else E)(label(t[1]),label(t[2]))
AND=lambda x,y:N(I(x,N(y)));EX=lambda i,x:N(Q(i,N(x)));XAO=lambda i,x,y:EX(i,AND(x,y))
wo=Q(b,I(m,XAO(b,m,r)));uo=Q(a,I(sub,wo));ho=Q(b,I(r,XAO(a,m,uo)));co=I(m,XAO(k,r,ho));unfused=AND(co,AND(VR,VE))
need(certform(cert['old_bundle'])==unfused,'Unfused conditional endpoint mismatch');need(certform(cert['fused_bundle'])==bundle,'Fused conditional endpoint mismatch')
res={'status':'INDEPENDENT_EXACT_CONDITIONAL223_SOURCE_PASS','source_sha256':sha((C/'sites.json').read_bytes()),'table_sha256':sha((C/'candidate223.k.tm').read_bytes()),'baseline_source_sha256':sha((P/'baseline_sites.json').read_bytes()),'emitter_contract_sha256':sha((P/'emitter_contract.json').read_bytes()),'replacement_path':occ[0],'all_other_source_context_unchanged':True,'exact_instruction_sequence':True,'exact_whole_source_guarded_cfg':True,'guarded_cfg_sha256':sha((json.dumps(G,separators=(',',':'))+'\n').encode()),'source_leaves':len(candidate_sites),'source_dag_nodes':len(allnodes),'guarded_cases':sum(2 if op=='CD'else 1 for _,op,_ in candidate_sites),'new_core':newcore,'new_bundle':bundle,'new_full_word':newword,'root_and_gate_nonhalting':'enabled fused bundle has root Imp, hence code0 mod4 and never1; disabled gate returns0','enumerator_rows':'old top, generalized cache, eight unchanged logical rows; current exact conditional bundle; no row deletion/permutation or changed field parsing','scope':'Arbitrary-register source semantics relative to the already verified fixed macro contracts, established by exact expanded instructions and whole guarded CFG identity. Independent of logical conditional-K calibration and TM runtime/startup. No sampled arithmetic is used.'}
res.update(fusion_certificate_sha256=sha(certpath.read_bytes()),fusion_unfused_endpoint_matches=True,fusion_fused_endpoint_matches=True,all_natural_parameters_including_coincidences=True)
(A/'conditional223_source.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps({k:v for k,v in res.items()if k not in ('new_core','new_bundle','new_full_word')},indent=2))
