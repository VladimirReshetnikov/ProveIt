#!/usr/bin/env python3
"""Finite joint strong/auxiliary sparse-Horner family; no historical imports."""
import argparse,hashlib,itertools,json,random
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
def need(x,m):
 if not x:raise ValueError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
PINS={'complete86_factored_first_root.py':'29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f','complete86_factored_first_root.md':'9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b','complete86_factored_first_root.json':'2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e'}

def polyadd(a,b,s=1):
 c=dict(a)
 for m,v in b.items():
  c[m]=c.get(m,0)+s*v
  if not c[m]:del c[m]
 return c
def polymul(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():
   p=tuple(x+y for x,y in zip(m,n));c[p]=c.get(p,0)+v*w
 return {m:v for m,v in c.items() if v}
def polyconst(x,d=5):return {(0,)*d:x} if x else {}
def polypow(a,n):
 c=polyconst(1,len(next(iter(a))))
 for _ in range(n):c=polymul(c,a)
 return c

def parts(n):
 def go(i,bs):
  if i==n:yield tuple(tuple(b) for b in bs);return
  for j in range(len(bs)):
   bs[j].append(i);yield from go(i+1,bs);bs[j].pop()
  bs.append([i]);yield from go(i+1,bs);bs.pop()
 yield from go(0,[])

class DAG:
 def __init__(self):self.rows=[];self.memo={}
 def gate(self,o,a,b):
  if type(a)is int and type(b)is int:return a+b if o=='+' else a-b if o=='-' else a*b
  if o=='+':
   if a==0:return b
   if b==0:return a
  if o=='-':
   if b==0:return a
   if a==b:return 0
  if o=='*':
   if a==0 or b==0:return 0
   if a==1:return b
   if b==1:return a
  if o in ('+','*') and repr(a)>repr(b):a,b=b,a
  key=(o,a,b)
  if key not in self.memo:
   self.memo[key]='g'+str(len(self.rows));self.rows.append([self.memo[key],o,a,b])
  return self.memo[key]
 def live(self,out):
  by={n:(o,a,b) for n,o,a,b in self.rows};seen=set()
  def walk(v):
   if type(v)is int or v not in by or v in seen:return
   seen.add(v)
   for x in by[v][1:]:walk(x)
  walk(out);return [r for r in self.rows if r[0] in seen]

def signed_add(d,a,b):
 s,x=a;t,y=b
 if x==0:return b
 if y==0:return a
 if s==t:return s,d.gate('+',x,y)
 return (1,d.gate('-',x,y)) if s==1 else (1,d.gate('-',y,x))
def signed_mul(d,a,b):return a[0]*b[0],d.gate('*',a[1],b[1])
def materialize(d,a):return a[1] if a[0]==1 else d.gate('-',0,a[1])

@lru_cache(None)
def binomial_factor(items):
 p=dict(items)
 if len(p)<3:return None
 candidates=set()
 for a,b in itertools.combinations(sorted(p),2):
  common=tuple(min(x,y) for x,y in zip(a,b))
  aa=tuple(x-y for x,y in zip(a,common));bb=tuple(x-y for x,y in zip(b,common))
  if p[a] not in (-1,1) or p[b] not in (-1,1):continue
  q={aa:p[a],bb:p[b]};sgn=q[max(q)];q={m:c*sgn for m,c in q.items()}
  candidates.add(tuple(sorted(q.items())))
 for choice in sorted(candidates):
  divisor=dict(choice);lead=max(divisor);remainder=dict(p);quotient={};ok=True
  while remainder:
   m=max(remainder)
   if any(a<b for a,b in zip(m,lead)):ok=False;break
   v=remainder[m];e=tuple(a-b for a,b in zip(m,lead));quotient[e]=quotient.get(e,0)+v
   remainder=polyadd(remainder,polymul({e:v},divisor),-1)
  if ok and len(quotient)>1:return choice,tuple(sorted(quotient.items()))
 return None

def horner_recipe(polynomial,partition,order,style,factor_binomials=False):
 d=DAG();inputs=['v'+str(i) for i in range(5)];memo={};power_memo={}
 def power(x,n):
  if n==0:return 1
  if n==1:return x
  key=x,n
  if key not in power_memo:
   p=power(x,n//2);q=d.gate('*',p,p);power_memo[key]=d.gate('*',q,x) if n%2 else q
  return power_memo[key]
 def mono(m):
  if style=='joint_square' and all(v%2==0 for v in m) and any(m):return power(mono(tuple(v//2 for v in m)),2)
  r=1
  for j in order:
   if m[j]:r=d.gate('*',r,power(inputs[j],m[j]))
  return r
 def emit(p,remaining):
  if not p:return 1,0
  sign=1 if p[max(p)]>0 else -1
  if sign<0:p={m:-v for m,v in p.items()}
  key=(tuple(sorted(p.items())),remaining)
  if key in memo:
   a=memo[key];return a[0]*sign,a[1]
  if len(p)==1:
   m,c=next(iter(p.items()));a=(1,d.gate('*',c,mono(m)))
  else:
   common=tuple(min(m[j] for m in p) for j in range(5))
   if any(common):
    pp={tuple(x-y for x,y in zip(m,common)):c for m,c in p.items()}
    a=signed_mul(d,(1,mono(common)),emit(pp,remaining))
   elif factor_binomials and binomial_factor(tuple(sorted(p.items()))) is not None:
    left,right=binomial_factor(tuple(sorted(p.items())));a=signed_mul(d,emit(dict(left),remaining),emit(dict(right),remaining))
   else:
    j=next(j for j in remaining if any(m[j] for m in p));rest=tuple(k for k in remaining if k!=j)
    groups={}
    for m,c in p.items():
     r=list(m);e=r[j];r[j]=0;groups.setdefault(e,{})[tuple(r)]=c
    exps=sorted(groups,reverse=True);a=emit(groups[exps[0]],rest);prev=exps[0]
    for e in exps[1:]:
     a=signed_mul(d,a,(1,power(inputs[j],prev-e)));a=signed_add(d,a,emit(groups[e],rest));prev=e
    if prev:a=signed_mul(d,a,(1,power(inputs[j],prev)))
  memo[key]=a;return a[0]*sign,a[1]
 terms=sorted(polynomial.items(),reverse=True);a=(1,0)
 for block in partition:a=signed_add(d,a,emit(dict(terms[i] for i in block),order))
 out=materialize(d,a);rows=d.live(out)
 return rows,out

def local_polynomial(rows,out):
 z=(0,)*5;env={}
 for j in range(5):m=list(z);m[j]=1;env['v'+str(j)]={tuple(m):1}
 def get(v):return polyconst(v) if type(v)is int else env[v]
 for n,o,a,b in rows:
  a=get(a);b=get(b);env[n]=polymul(a,b) if o=='*' else polyadd(a,b,1 if o=='+' else -1)
 return get(out)

def charts():
 v=[]
 for j in range(5):m=[0]*5;m[j]=1;v.append({tuple(m):1})
 F,Q,K,U,Y=v
 p=polymul(polyadd(F,Q,-1),polyadd(polymul(K,polyadd(U,Y,-1)),Y))
 result=[('QK',p,['L16','strong_difference','R16','H2','aux_y2'],'separate_powers')]
 F,Q,A,U,Y=v;p=polymul(polyadd(F,Q,-1),polyadd(polymul(polymul(A,Q),polyadd(U,Y,-1)),Y))
 result.append(('QA',p,['L16','strong_difference','A','H2','aux_y2'],'separate_powers'))
 F,T,A,U,Y=v;p=polymul(polyadd(F,polymul(A,T),-1),polyadd(polymul(polymul(polypow(A,2),T),polyadd(U,Y,-1)),Y))
 result.append(('T2A',p,['L16','ic22','A','H2','aux_y2'],'separate_powers'))
 F,t,H,U,Y=v;p=polymul(polyadd(F,polymul(t,H),-1),polyadd(polymul(polypow(H,2),polyadd(U,Y,-1)),Y))
 result.append(('tH',p,['L16','ic2','shared_H','H2','aux_y2'],'separate_powers'))
 f,t,H,V,y=v;p=polymul(polyadd(polypow(f,2),polymul(t,H),-1),polyadd(polymul(polypow(H,2),polyadd(polypow(V,2),polypow(y,2),-1)),polypow(y,2)))
 for style in ('separate_powers','joint_square'):result.append(('raw_tH_'+style,p,['f','ic2','shared_H','aux_u_rhs','y_aux'],style))
 return result

def emit_full(old,ports,local,out):
 d=DAG();nodes={n:(o,a,b) for n,o,a,b in old};nodes['shared_H']=('*','i','Ac2');aliases={};active=set();joint=[None]
 def get(v):
  if type(v)is int or v not in nodes:return v
  if v in aliases:return aliases[v]
  need(v not in active,'cycle');active.add(v)
  if v=='seven_units':res=get('all_units')
  elif v=='norm_four':res=d.gate('*',get('norm_triple'),joint_get())
  else:
   o,a,b=nodes[v];res=d.gate(o,get(a),get(b))
  active.remove(v);aliases[v]=res;return res
 def joint_get():
  if joint[0] is None:
   e={'v'+str(i):get(p) for i,p in enumerate(ports)}
   def val(x):return x if type(x)is int else e[x]
   for n,o,a,b in local:e[n]=d.gate(o,val(a),val(b))
   joint[0]=val(out)
  return joint[0]
 final=get('polynomial');rows=d.live(final)
 return {'source':rows,'output':final,'joint_output':joint[0],'aliases':{k:v for k,v in aliases.items() if type(v)is int or v in {r[0] for r in rows}}}

def source_info(rows,out):
 names={r[0] for r in rows};need(len(names)==len(rows),'duplicate')
 free={x for _,_,a,b in rows for x in (a,b) if type(x)is str and x not in names};seen=set(free);nodes={}
 for n,o,a,b in rows:
  need(type(n)is str and n not in seen and o in ['+','-','*'],'schema')
  need(all(type(x)is int or type(x)is str and x in seen for x in (a,b)),'topology');seen.add(n);nodes[n]=(a,b)
 live=set()
 def visit(x):
  if type(x)is int or x in free or x in live:return
  live.add(x)
  for y in nodes[x]:visit(y)
 visit(out);need(live==names,'dead gate');c=Counter(r[1] for r in rows)
 return {'operations':len(rows),'M':c['*'],'A':c['+']+c['-'],'free':sorted(free),'live':len(live)}
def run(rows,out,values):
 e=dict(values)
 def g(v):return v if type(v)is int else e[v]
 for n,o,a,b in rows:
  a=g(a);b=g(b);e[n]=a+b if o=='+' else a-b if o=='-' else a*b
 return g(out)

FACTORS=('norm_first','norm_main','norm_input','norm_index','norm_transport','norm_linear')
def proof_factory(old):
 table={}
 def intern(x):
  if x not in table:table[x]=len(table)
  return table[x]
 def signatures(rows,outputs):
  nodes={n:(o,a,b) for n,o,a,b in rows};memo={}
  def get(x):
   if type(x)is int:return intern(('integer',x))
   if x not in nodes:return intern(('input',x))
   if x not in memo:
    o,a,b=nodes[x];a=get(a);b=get(b)
    if o in ('+','*') and b<a:a,b=b,a
    memo[x]=intern((o,a,b))
   return memo[x]
  return [get(x) for x in outputs]
 wanted=signatures(old,FACTORS)
 basis=[]
 for j in range(8):m=[0]*8;m[j]=1;basis.append({tuple(m):1})
 expected={(1,)*8:1,(0,)*8:-1}
 def cutpoly(rows,out,cuts):
  nodes={n:(o,a,b) for n,o,a,b in rows};memo=dict(cuts)
  def get(x):
   if type(x)is int:return polyconst(x,8)
   if x not in memo:
    need(x in nodes,'unproved finalizer free input '+x);o,a,b=nodes[x];a=get(a);b=get(b)
    memo[x]=polymul(a,b) if o=='*' else polyadd(a,b,1 if o=='+' else -1)
   return memo[x]
  return get(out)
 need(cutpoly(old,'polynomial',{**{n:basis[j] for j,n in enumerate(FACTORS)},'norm_strong':basis[6],'norm_aux':basis[7]})==expected,'parent complete finalizer')
 def prove(packet):
  got=signatures(packet['source'],[packet['aliases'][n] for n in FACTORS]);need(got==wanted,'retained complete factor DAG identity')
  cuts={packet['aliases'][n]:basis[j] for j,n in enumerate(FACTORS)};cuts[packet['joint_output']]=polymul(basis[6],basis[7])
  need(cutpoly(packet['source'],packet['output'],cuts)==expected,'entire grouped finalizer identity')
 return prove

def chart_proof(chart):
 _,p,ports,_=chart;v=[]
 for j in range(6):m=[0]*6;m[j]=1;v.append({tuple(m):1})
 A,i,c,f,V,y=v;t=polymul(i,polypow(c,2));H=polymul(A,t);Q=polymul(A,polypow(t,2));K=polymul(A,Q)
 values={'A':A,'ic2':t,'ic22':polypow(t,2),'shared_H':H,'L16':polypow(f,2),'strong_difference':Q,'R16':K,'H2':polypow(V,2),'aux_y2':polypow(y,2),'f':f,'aux_u_rhs':V,'y_aux':y}
 result={}
 for m,coefficient in p.items():
  term=polyconst(coefficient,6)
  for e,port in zip(m,ports):term=polymul(term,polypow(values[port],e))
  result=polyadd(result,term)
 target=polymul(polyadd(polypow(f,2),Q,-1),polyadd(polymul(K,polyadd(polypow(V,2),polypow(y,2),-1)),polypow(y,2)))
 need(result==target,'actual paid-port chart substitution')
 return True

def verify(root):
 for name,h in PINS.items():need(sha((root/name).read_bytes())==h,'pin '+name)
 parent=json.loads((root/'complete86_factored_first_root.json').read_text())['forms'][0];old=parent['source'];base=source_info(old,'polynomial')
 need((base['operations'],base['M'],base['A'])==(86,48,38),'actual86')
 d=DAG();e={}
 for n,o,a,b in old:e[n]=d.gate(o,e.get(a,a),e.get(b,b))
 need(source_info(d.live(e['polynomial']),e['polynomial'])==base,'fair baseline CSE/folding')
 prove=proof_factory(old)
 for chart in charts():chart_proof(chart)
 # Exact literal prerequisites and sole consumers of the two final factors.
 expected={'ic2':('*','i','c2'),'ic22':('*','ic2','ic2'),'strong_difference':('*','A','ic22'),'R16':('*','A','strong_difference'),'L16':('*','f','f'),'norm_strong':('-','L16','strong_difference'),'c2':('*','R10a','R10a'),'Ac2':('*','A','c2'),'aux_u_rhs':('-','of','R10a'),'H2':('*','aux_u_rhs','aux_u_rhs'),'aux_y2':('*','y_aux','y_aux'),'aux_square_gap':('-','H2','aux_y2'),'L17':('*','R16','aux_square_gap'),'norm_aux':('+','L17','aux_y2')}
 nodes={n:(o,a,b) for n,o,a,b in old}
 for k,v in expected.items():need(nodes[k]==v,'literal block '+k)
 consumers={k:[n for n,o,a,b in old for v in(a,b) if v==k] for k in ('norm_aux','norm_strong')}
 need(consumers=={'norm_aux':['norm_four'],'norm_strong':['seven_units']},'private final factors')
 partitions=list(parts(6));orders=list(itertools.permutations(range(5)));need(len(partitions)==203 and len(orders)==120,'finite family')
 summaries=[];best_packets=[];proofs=0;forms=0;global_digest=hashlib.sha256();distinct_all=set();numerical=0;rational=0;rng=random.Random(860602)
 for rawname,p,ports,style,binomials in [(n,p,ps,s,b) for n,p,ps,s in charts() for b in (False,True)]:
  name=rawname+('_binomial_factors' if binomials else '_monomial_factors')
  need(len(p)==6,'six terms');hist=Counter();best=None;representative=None;seen={};local_proofs=0;chart_digest=hashlib.sha256()
  for partition in partitions:
   for order in orders:
    local,out=horner_recipe(p,partition,order,style,binomials);key=json.dumps([local,out],separators=(',',':'));hk=sha(key.encode())
    if hk not in seen:
     need(local_polynomial(local,out)==p,'joint coefficient identity');local_proofs+=1
     pkt=emit_full(old,ports,local,out);led=source_info(pkt['source'],pkt['output']);need(led['free']==base['free'],'exact free set');prove(pkt)
     seen[hk]=(led,pkt);distinct_all.add((name,hk))
    led,pkt=seen[hk];cost=(led['operations'],led['M'],led['A']);hist[cost]+=1;forms+=1
    chart_digest.update(json.dumps([partition,order,hk,cost],separators=(',',':')).encode())
    if best is None or cost<best:
     best=cost;representative={'chart':name,'partition':[list(x) for x in partition],'order':list(order),'style':style,'binomial_factorization':binomials,'local_source':local,'local_output':out,'ports':ports,'ledger':led,**pkt}
  proofs+=local_proofs;global_digest.update(chart_digest.digest())
  summaries.append({'chart':name,'choices':sum(hist.values()),'distinct_local_sources':len(seen),'exact_local_polynomial_proofs':local_proofs,'best':list(best),'histogram':[{'cost':list(c),'choices':n} for c,n in sorted(hist.items())],'ordered_census_sha256':chart_digest.hexdigest()})
  best_packets.append(representative)
  for case in range(32):
   values={k:rng.randrange(-3,4) if case%2 else rng.randrange(1,5) for k in base['free']}
   if case>=24:
    values={k:Fraction(v,1+(j%3)) for j,(k,v) in enumerate(values.items())};rational+=1
   need(run(old,'polynomial',values)==run(representative['source'],representative['output'],values),'whole source numeric');numerical+=1
 # Explicit original factorized schedule is the comparison, not one artificial
 # term-partition count. The result remains a finite grammar, not a lower bound.
 need(forms==292320 and proofs==58113,'fixed complete census');need(min(x['best'][0] for x in summaries)==86,'bounded minimum changed')
 return {'status':'PASS_BOUNDED_NO_IMPROVEMENT','source_sha256':sha(Path(__file__).read_bytes()),'parent_pins':PINS,'baseline':base,'factor_consumers':consumers,'literal_block_checks':len(expected),'set_partitions':203,'orders_per_chart':120,'chart_count':6,'factorization_modes':2,'choices':forms,'distinct_local_source_proofs':proofs,'whole_finalizer_identities':proofs,'retained_factor_DAG_identities':6*proofs,'paid_chart_substitution_identities':6,'ordered_census_sha256':global_digest.hexdigest(),'whole_numeric_comparisons':numerical,'signed_numeric_comparisons':numerical//2,'rational_comparisons':rational,'summaries':summaries,'best_sources':best_packets,'exact_degree':179,'scope':'Six explicitly defined paid charts; every six-monomial set partition, every common five-variable Horner order, two declared factoring modes and monomial-power schedule only. No general lower bound, coordinate projection, or universal improvement.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root);r=json.loads(json.dumps(r))
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'saved receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['choices'],r['distinct_local_source_proofs'],[(x['chart'],x['best']) for x in r['summaries']])
if __name__=='__main__':main()
