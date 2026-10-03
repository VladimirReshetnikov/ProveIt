#!/usr/bin/env python3
"""Bounded independent review of saved complete endpoint circuits; no imports."""
import argparse,hashlib,json
from collections import Counter
from pathlib import Path
SOURCE='7010ab32c2ac44a84ea61f4393b826cdc1401c654f20364dbad7f694e3eb605c'
RECEIPT='10cbe0a62be35c03da5e9902e88c55b457c28b3c7295026fb6f33472dbdc82c8'
def need(v,s):
 if not v:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def add(p,q,k=1):
 o=p.copy()
 for m,c in q.items():o[m]=o.get(m,0)+k*c
 return {m:c for m,c in o.items() if c}
def mul(p,q):
 o={}
 for m,c in p.items():
  for n,d in q.items():
   key=tuple(sorted(m+n));o[key]=o.get(key,0)+c*d
 return {m:c for m,c in o.items() if c}
def expand(cert):
 f=cert.get('forward_certificate',cert);pair={r['u']:r['e'] for step in f['steps'] for r in step}
 def aff(form):
  o={}
  for n,c in form.items():
   need(type(c)is int,'Exact original coefficient')
   v={():1} if not n else {('v'+n[1:],):1,(pair[n],):-1} if n in pair else {(n,):1}
   o=add(o,{m:c*d for m,d in v.items()})
  return o
 rows={r['label']:aff(r['affine']) for r in cert['squares']};F={}
 for p in rows.values():F=add(F,mul(p,p))
 for r in cert['products']:F=add(F,mul(aff(r['left']),aff(r['right'])))
 G=F.copy();K={}
 if f['horizon']:
  for label in ('step-0:control','terminal:halt'):G=add(G,mul(rows[label],rows[label]),-1)
  for row,b in zip(f['steps'][0],f['branches']):
   if b['source']!=f['initial_state']:K=add(K,{(row['e'],):1})
  for row,b in zip(f['steps'][-1],f['branches']):
   if b['target']!=f['machine']['halt']:K=add(K,{(row['e'],):1})
  G=add(G,K)
 return F,G,K

def check(p,want):
 env={n:{(n,):1} for n in p['variables']};deps={};ops=Counter()
 def atom(v):
  if type(v)is str:need(v in env,'Topological closure');return env[v]
  need(type(v)is int,'Exact integer literal');return {():v} if v else {}
 for n,op,a,b in p['source']:
  need(n not in env and op in ('+','-','*'),'Fresh binary operation')
  pa,pb=atom(a),atom(b);env[n]=mul(pa,pb) if op=='*' else add(pa,pb,1 if op=='+' else -1)
  deps[n]=[v for v in (a,b) if v in deps];ops[op]+=1
 need(atom(p['output'])==want,'Complete polynomial independently reconstructed')
 need(max(map(len,want),default=0)==2 and want.get(('T','T'))==1,'Exact quadratic degree and paid clock')
 need(atom(p['ports']['N0'])=={('x',):1,():1},'Paid x+1')
 live=set()
 def visit(n):
  if n in deps and n not in live:
   live.add(n)
   for v in deps[n]:visit(v)
 visit(p['output']);need(live==set(deps),'Every paid gate live')
 ledger={'M':ops['*'],'A':ops['+']+ops['-'],'total':len(deps)}
 need(exact(ledger,p['ledger']),'Complete independent ledger')
 return ledger,len(deps)

def run(source,receipt):
 need(sha(Path(source).read_bytes())==SOURCE,'Source pin')
 b=Path(receipt).read_bytes();need(sha(b)==RECEIPT,'Receipt pin');r=json.loads(b);counts=Counter();cases=[]
 for row in r['cases']:
  if row['full_packets']is None:continue
  cert=row['certificate'];F,G,K=expand(cert);ledgers={}
  for schedule,pair in row['full_packets'].items():
   old,n=check(pair['old'],F);new,m=check(pair['new'],G);counts['complete_pair_polynomial_identities']+=1;counts['live_paid_gates']+=n+m
   need(pair['old']['variables']==pair['new']['variables'],'Coordinate identity')
   need(pair['old']['natural_witnesses']==pair['new']['natural_witnesses'],'Witness count unchanged')
   ledgers[schedule]={'old':old,'new':new}
  cases.append({'fixture':row['fixture'],'horizon':row['horizon'],'clean':row['clean'],'ledgers':ledgers})
 return {'source_sha256':SOURCE,'author_receipt_sha256':RECEIPT,'counts':dict(counts),'cases':cases,'scope':'Seven saved actual certificates,14 full old/new pairs; complete source and companion proof read separately. No author suites or hostile API audit.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--source',required=True);p.add_argument('--receipt',required=True);p.add_argument('--output',required=True);p.add_argument('--expect');a=p.parse_args();r=run(a.source,a.receipt)
 if a.expect:need(exact(r,json.loads(Path(a.expect).read_text())),'Typed saved review receipt')
 Path(a.output).write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(json.dumps(r['counts']))
