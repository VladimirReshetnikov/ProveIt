#!/usr/bin/env python3
"""Expand the pinned Coq proof text to a self-contained restricted-rho8 DAG.

This is a certificate *builder*.  The separate checker does only forward
substitution, axiom matching, and modus ponens; it trusts neither this script
nor Coq/Prover9 proof searches.
"""
import json,re,sys,hashlib
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import extract_cd59 as c

HERE=Path(__file__).resolve().parent
src=HERE/'evidence/CD230.v'
if not src.exists():src=HERE.parent/'prior_reports/research218_progress_latex/research218_companion/evidence/logic/CD230.v'
S=src.read_text()

def norm(t):
 if not isinstance(t,(list,tuple)):return t
 a,b=map(norm,t)
 return 'T' if a==b=='T' else (a,b)
def I(a,b):return norm((a,b))
def contains(a,u):return a==u or isinstance(a,tuple) and any(contains(v,u) for v in a)
def subst(t,e):
 if isinstance(t,tuple):return I(subst(t[0],e),subst(t[1],e))
 return e[t] if isinstance(t,int) else t

def parse(s):
 ts=re.findall(r'cd_\d+|T_mp|wim|v\d+|\d+|_|[()]',s);i=0
 def one():
  nonlocal i
  t=ts[i];i+=1
  if t!='(':return t
  z=[]
  while ts[i]!=')':z.append(one())
  i+=1;return tuple(z)
 out=[]
 while i<len(ts):out.append(one())
 return tuple(out)
lem={}
for m in re.finditer(r'Lemma cd_(\d+) \((.*?) : nat\) : thm230 (.*?)\.\s*Proof\. exact \((.*?)\)\. Qed\.',S,re.S):
 lem[int(m[1])]=(m[2].split(),parse(m[3])[0],parse(m[4]))
assert len(lem)==107

def term(t,env):
 if isinstance(t,str):return env[t]
 assert t[0]=='wim' and len(t)==3,t
 return I(term(t[1],env),term(t[2],env))
def statement(n,args):
 vs,t,_=lem[n];assert len(vs)==len(args)
 return term(t,dict(zip(vs,args))|{'0':'T'})

roots={'I':c.oldadd(140),'K':c.oldadd(160),'P':c.oldadd(349),'cd59':c.root}
terms=[norm(x['term']) for x in c.new]
node_for={t:i for i,t in enumerate(terms)}
def add(t,rule,origin):
 t=norm(t)
 if t in node_for:return node_for[t]
 i=c.add(t,rule,origin);terms.append(t);node_for[t]=i;return i

def match(p,t,e):
 if isinstance(p,int):
  if p in e:assert e[p]==t
  else:e[p]=t
 elif p=='T':assert t=='T'
 else:
  if t=='T':t=('T','T')
  assert isinstance(t,tuple)
  match(p[0],t[0],e);match(p[1],t[1],e)

def inst(root,t,origin):
 e={};match(terms[root],t,e)
 assert subst(terms[root],e)==t
 return add(t,{'kind':'substitution','parent':root,'substitution':e},origin)
def mp(mi,ma,origin):
 major=terms[ma] if terms[ma]!='T' else ('T','T')
 assert isinstance(major,tuple),(origin,ma)
 assert major[0]==terms[mi],(origin,major[0],terms[mi])
 return add(major[1],{'kind':'mp','major':ma,'minor':mi},origin)

def simple(t):
 if t in node_for:return node_for[t]
 for name in roots:
  try:return inst(roots[name],t,'basis_instance:'+name)
  except AssertionError:pass
 assert isinstance(t,tuple),t
 h=simple(t[1])
 k=inst(roots['K'],I(t[1],t),'weakening_K')
 return mp(h,k,'weakening_MP')

base={2,3,6,8,9,12,13,15,16,17,25,39,40,59}
memo={};leaf_count=0

def prove(n,args):
 global leaf_count
 key=(n,args)
 if key in memo:return memo[key]
 wanted=statement(n,args)
 if wanted in node_for:
  memo[key]=node_for[wanted];return memo[key]
 if n in base:
  result=simple(wanted)
 elif n==0:
  C,U,A,B=args
  assert U=='T' or contains(A,U),('undominated',key)
  result=add(wanted,{'kind':'dominated_rho8'},'CD230:cd_0');leaf_count+=1
 else:
  vs,_,body=lem[n];env=dict(zip(vs,args))|{'0':'T'}
  def walk(b):
   if b[0]=='T_mp':
    assert len(b)==5 and b[1:3]==('_','_'),b[:3]
    mi=walk(b[3]);ma=walk(b[4]);return mp(mi,ma,'CD230:cd_'+str(n))
   assert b[0].startswith('cd_'),b
   k=int(b[0][3:]);return prove(k,tuple(term(x,env)for x in b[1:]))
  result=walk(body)
 assert terms[result]==wanted,('statement mismatch',n)
 memo[key]=result;return result

roots['B']=prove(91,(0,1,2));base.add(91)
roots['S']=prove(106,(0,1,2))
# No merely conditional base nodes remain: every node has a primitive rule.
assert all(n['rule']['kind'] in {'truth','dominated_rho8','mp_substitution','substitution','mp'} for n in c.new)
result={'theorem':'Classical_basis_from_dominated_rho8','claim':'The raw natural-number calculus with truth0, MP, and rho8(A,B,C,U) restricted to U<=A proves I,K,Peirce,B,S for all natural arguments.','implication_code':'I(a,b)=4*((a+b)*(a+b+1)//2+b)','truth_code':0,'roots':roots,'nodes':c.new,'sources':{'CD230_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'cd59_certificate':'cd59_certificate.json'},'limits':'Finite source-theory certificate; no binary-runtime claim.'}
# Share term subtrees explicitly; this makes the proof independently checkable
# without inflating repeated long substitutions into hundreds of megabytes.
term_table=[];term_ids={}
def intern(t):
 t=norm(t)
 if t in term_ids:return term_ids[t]
 entry=[intern(t[0]),intern(t[1])] if isinstance(t,tuple) else {'var':t} if isinstance(t,int) else 'T'
 j=len(term_table);term_ids[t]=j;term_table.append(entry);return j
compact=[]
for node in c.new:
 nn=dict(node);nn['term']=intern(node['term']);rr=dict(nn['rule'])
 for field in ['substitution','major_substitution','minor_substitution']:
  if field in rr:rr[field]={k:intern(v)for k,v in rr[field].items()}
 nn['rule']=rr;compact.append(nn)
result['nodes']=compact;result['term_table']=term_table;result['format']='term_dag_v1'
out=(HERE/'classical_basis_certificate_compact.json');out.write_text(json.dumps(result,separators=(',',':'))+'\n')
print(json.dumps({'nodes':len(c.new),'terms':len(term_table),'roots':roots,'expanded_coq_calls':len(memo),'new_dominated_leaves':leaf_count,'bytes':out.stat().st_size},indent=2))
