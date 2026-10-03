#!/usr/bin/env python3
"""Bounded, fully paid index/quotient affine-shift scout for three complete74 sources.
No parent module is imported. Public scope is the source-pinned CLI receipt.
"""
import argparse,copy,hashlib,itertools,json,random,sys
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={
 'complete74_factored_first_norm.py':'7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908',
 'complete74_factored_first_norm.json':'7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28',
 'complete74_factored_first_norm.md':'119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f',
 'complete75_signed_projection_elimination101.md':'55b701410d05b515b6cbc4619a3f39fc290f469d21d03dfee9e291aa674fa31d',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117'}
MODES=('raw30','positive22','signed20')
PORTS=('r','j','h','zquot')
def need(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def sha(b):return hashlib.sha256(b).hexdigest()
def pins(root,manifest):
 out={}
 for n,h in manifest.items():
  b=(Path(root)/n).read_bytes();need(sha(b)==h,'Pinned blob '+n);out[n]=b
 return out
def numeric(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a+b if o=='+'else a-b if o=='-'else a*b
 return e

def ledger(rows,free,outputs,fixed=()):
 known=set(free);defs={};degree={x:0 if x in fixed else 1 for x in free}
 for row in rows:
  need(type(row)is list and len(row)==4,'literal row');n,o,a,b=row
  need(type(n)is str and n not in known and o in('+','-','*'),'fresh exact gate')
  need(all(type(x)is int or type(x)is str and x in known for x in(a,b)),'source closure')
  da=degree[a]if type(a)is str else 0;db=degree[b]if type(b)is str else 0
  degree[n]=da+db if o=='*'else max(da,db);known.add(n);defs[n]=(a,b)
 live=set();stack=list(outputs)
 while stack:
  x=stack.pop()
  if type(x)is int or x in live:continue
  live.add(x);stack.extend(defs.get(x,()))
 need(set(defs)|set(free)<=live,'all paid rows/coordinates live')
 M=sum(r[1]=='*'for r in rows)
 return M,len(rows)-M,max(degree[x]if type(x)is str else 0 for x in outputs)
class RingDAG:
 # Linear combinations of opaque product atoms. Addition normalizes exact
 # coefficients; multiplication extracts scalar signs but never expands sums.
 def __init__(self):self.ids={('one',):0}
 def node(self,key):
  if key not in self.ids:self.ids[key]=len(self.ids)
  return self.ids[key]
 def val(self,x):return ((0,x),)if type(x)is int and x else()if type(x)is int else((self.node(('var',x)),1),)
 def scale(self,e,c):return tuple((k,v*c)for k,v in e)if c else()
 def add(self,a,b,sign=1):
  e=dict(a)
  for n,c in b:e[n]=e.get(n,0)+sign*c
  return tuple(sorted((n,c)for n,c in e.items()if c))
 def mul(self,a,b):
  if not a or not b:return()
  if len(a)==1 and a[0][0]==0:return self.scale(b,a[0][1])
  if len(b)==1 and b[0][0]==0:return self.scale(a,b[0][1])
  sa=-1 if a[0][1]<0 else 1;sb=-1 if b[0][1]<0 else 1
  a=self.scale(a,sa);b=self.scale(b,sb)
  if a>b:a,b=b,a
  return((self.node(('mul',a,b)),sa*sb),)
 def run(self,rows,free,replacements=None):
  e={n:self.val(n)for n in free};e.update(replacements or{})
  for n,o,a,b in rows:
   a=e[a]if type(a)is str else self.val(a);b=e[b]if type(b)is str else self.val(b)
   e[n]=self.mul(a,b)if o=='*'else self.add(a,b,1 if o=='+'else -1)
  return e



def finalize(rows,pairs):
 out=copy.deepcopy(rows)
 for i,(a,b)in enumerate(pairs):out.extend([[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']])
 name='square_0'
 for i in range(1,len(pairs)):
  n=f'sum_{i}';out.append([n,'+',name,f'square_{i}']);name=n
 return out,name

def consumers(p,n):
 return {'source':[r[0]for r in p['source']if n in r[2:]],'comparisons':[i for i,pair in enumerate(p['comparisons'])if n in pair]}

def check_parent(p):
 rows=p['source'];pairs=p['comparisons'];d={n:(o,a,b)for n,o,a,b in rows};mode=p['mode']
 c='c'if mode=='raw30'else'R10a';k='k'if mode=='raw30'else'R10b'
 need(d['r1']==('+','r',1)and d['hpm1']==('*','h','UM')and d['R11']==('+','r1','hpm1'),'actual index cone')
 need(d['jc']==('*','j',c)and d['H17']==('-','jc','r')and d['aux_u_rhs']==('-','of',c)and d['of']==('*','o','f'),'actual auxiliary cone')
 need(d['H2']==('*','H17','H17')and ['H17','aux_u_rhs']in pairs,'norm and auxiliary comparison both retained')
 need(d['ksn2']==('*',k,'sn2')and d['first_next']==('+','first_root_base',k),'actual supplied or computed k is retained')
 need(consumers(p,'r')=={'source':['r1','H17'],'comparisons':[pairs.index(['r','r_lhs'])]},'all three r consumers')
 need(consumers(p,'j')=={'source':['jc'],'comparisons':[]}and consumers(p,'h')=={'source':['hpm1'],'comparisons':[]},'literal single j/h consumers')
 need(consumers(p,'zquot')=={'source':['local_rhs'],'comparisons':[]}and consumers(p,'r1')=={'source':['R11'],'comparisons':[]},'literal quotient and r1 privacy')
 need(consumers(p,'jc')=={'source':['H17'],'comparisons':[]}and consumers(p,'aux_u_rhs')=={'source':[],'comparisons':[pairs.index(['H17','aux_u_rhs'])]},'private auxiliary row outputs')
 need(d['local_rhs']==('*','zquot','qm1'if mode=='raw30'else'repunit'),'actual transport quotient product')
 need(d['rproduct']==('*','gap','Lm1')and d['r_lhs']==('+','rproduct','mask')and d['mask']==('*','mask_factor','Jrep')and d['mask_factor']==('+','MC','qMF')and d['qMF']==('*','q','MF'),'actual packing mask cone')
 poly,out=finalize(rows,pairs);need(poly==p['polynomial_source']and out==p['output'],'complete literal parent finalizer')
 free=p['fixed_numerals']+p['witnesses']+[p['ordinary_input']]
 need(ledger(rows,free,[v for pair in pairs for v in pair],p['fixed_numerals'])[:2]==(40,34),'actual 74 parent ledger')
 return c

def build(p,shifts):
 need(type(shifts)is tuple and len(shifts)==4 and all(type(s)is int and s in(-1,0,1)for s in shifts),'finite exact recipe')
 c=check_parent(p);sh=dict(zip(PORTS,shifts));aliases={};rows=[]
 for n,s in sh.items():
  if s and not(n=='j'and s==1):
   dest=f'shifted_old_{n}';rows.append([dest,'-'if s==1 else'+',n,1]);aliases[n]=dest
 for n,o,a,b in p['source']:
  if n=='r1'and sh['r']==1:aliases[n]='r';continue
  if n=='aux_u_rhs'and sh['j']==1:continue
  a=aliases.get(a,a);b=aliases.get(b,b)
  if n=='H17'and sh['j']==1:
   rows.extend([['shifted_H17_before_c','-',a,b],['H17','-','shifted_H17_before_c',c]])
  else:rows.append([n,o,a,b])
 pairs=[[aliases.get(a,a),aliases.get(b,b)]for a,b in p['comparisons']]
 if sh['j']==1:pairs[p['comparisons'].index(['H17','aux_u_rhs'])]=['shifted_H17_before_c','of']
 poly,out=finalize(rows,pairs)
 return dict(mode=p['mode'],shifts=sh,coordinate_map='old port = supplied port - declared shift',source=rows,comparisons=pairs,polynomial_source=poly,output=out,witnesses=p['witnesses'],fixed_numerals=p['fixed_numerals'],ordinary_input=p['ordinary_input'],exact_polynomial_degree=p['exact_polynomial_degree'],positive_zero_bijection_proved=sh['r']in(0,1)and sh['j']in(0,1)and sh['h']==sh['zquot']==0)

# Independent small coefficient dictionaries establish the only distributive cut.
def padd(a,b,s=1):
 r=dict(a)
 for k,v in b.items():r[k]=r.get(k,0)+s*v
 return{k:v for k,v in r.items()if v}
def pmul(a,b):
 r={}
 for u,x in a.items():
  for v,y in b.items():
   k=tuple(i+j for i,j in zip(u,v));r[k]=r.get(k,0)+x*y
 return{k:v for k,v in r.items()if v}
def cuts():
 one={(0,0,0,0):1};v=[{tuple(int(j==i)for j in range(4)):1}for i in range(4)];j,c,r,of=v
 oldH=padd(pmul(padd(j,one,-1),c),r,-1);pre=padd(pmul(j,c),r,-1);newH=padd(pre,c,-1)
 need(oldH==newH,'exact expanded auxiliary norm port')
 need(padd(oldH,padd(of,c,-1),-1)==padd(pre,of,-1),'exact expanded auxiliary comparison')
 # Literal old H and the new pre-H can now be replaced by H and H+c.
 return {'old_H_terms':len(oldH),'linear_residual_terms':len(padd(pre,of,-1)),'identities':2}

def symbolic(p,q,c):
 ring=RingDAG();free=p['fixed_numerals']+p['witnesses']+[p['ordinary_input']]
 substitutions={n:ring.add(ring.val(n),ring.val(s),-1)for n,s in q['shifts'].items()if s}
 def run(rows,old):
  e={n:ring.val(n)for n in free}
  if old:e.update(substitutions)
  for n,o,a,b in rows:
   a=e[a]if type(a)is str else ring.val(a);b=e[b]if type(b)is str else ring.val(b)
   e[n]=ring.mul(a,b)if o=='*'else ring.add(a,b,1 if o=='+'else -1)
   if q['shifts']['j']==1:
    if old and n=='H17':e[n]=ring.val('proved_auxiliary_H')
    if not old and n=='shifted_H17_before_c':e[n]=ring.add(ring.val('proved_auxiliary_H'),e[c])
  return e
 old=run(p['polynomial_source'],True);new=run(q['polynomial_source'],False)
 for i in range(len(p['comparisons'])):need(old[f'residual_{i}']==new[f'residual_{i}'],'every full residual under affine pullback')
 need(old[p['output']]==new[q['output']],'entire literal SOS under affine pullback')
 return len(p['comparisons'])

def verify(root):
 blobs=pins(root,PINS);parents=json.loads(blobs['complete74_factored_first_norm.json']);need(tuple(f['mode']for f in parents['forms'])==MODES,'exact three parent modes')
 local=cuts();rng=random.Random(742026);census=[];selected=[];totals=Counter();histograms={};privacy={}
 expected={(mode,*sh)for mode in MODES for sh in itertools.product((-1,0,1),repeat=4)};seen=set()
 for f in parents['forms']:
  p=f['packet'];c=check_parent(p);free=p['fixed_numerals']+p['witnesses']+[p['ordinary_input']];hist=Counter();privacy[p['mode']]={n:consumers(p,n)for n in PORTS+('r1','jc','aux_u_rhs')}
  for sh in itertools.product((-1,0,1),repeat=4):
   q=build(p,sh);seen.add((p['mode'],*sh));e=len(q['comparisons']);M,A,D=ledger(q['source'],free,[v for pair in q['comparisons']for v in pair],p['fixed_numerals']);PM,PA,PD=ledger(q['polynomial_source'],free,[q['output']],p['fixed_numerals'])
   extra=int(sh[0]==-1)+int(sh[1]==-1)+int(sh[2]!=0)+int(sh[3]!=0)
   need((M,A,PM,PA)==(40,34+extra,40+e,34+extra+2*e-1),'all-consumer complete ledgers')
   need(PD==ledger(p['polynomial_source'],free,[p['output']],p['fixed_numerals'])[2],'literal propagated degree bound unchanged')
   counts={'M':M,'A':A,'operations':M+A,'all_gates_live':True};polycounts={'M':PM,'A':PA,'operations':PM+PA,'all_gates_live':True}
   q.update(certificate_ledger=counts,polynomial_ledger=polycounts,degree_proof='exact parent polynomial under invertible constant affine translation; unchanged highest homogeneous part')
   totals['residual_identities']+=symbolic(p,q,c);totals['complete_polynomial_identities']+=1;totals['paid_live_polynomial_gates']+=PM+PA;totals['complete_sources']+=1;totals['degree_transfers']+=1
   for case in range(4):
    v={n:rng.randrange(-2,4)for n in free}
    if case==0:v={n:rng.randrange(1,4)for n in free}
    if case==3:v={n:Fraction(z,3)for n,z in v.items()};totals['rational_cases']+=1
    vo=dict(v)
    for n,s in q['shifts'].items():vo[n]-=s
    old=numeric(p['polynomial_source'],vo);new=numeric(q['polynomial_source'],v)
    need(old[p['output']]==new[q['output']],'full exact numeric affine identity');totals['numeric_complete_identities']+=1
    for i in range(e):need(old[f'residual_{i}']==new[f'residual_{i}'],'every numeric residual');totals['numeric_residual_identities']+=1
   srcsha=sha(json.dumps(q['source'],separators=(',',':')).encode());hist[M+A]+=1
   census.append(dict(mode=p['mode'],shifts=list(sh),certificate=counts,polynomial=polycounts,witnesses=len(p['witnesses']),equations=e,exact_degree=p['exact_polynomial_degree'],propagated_degree_upper=PD,positive_zero_bijection_proved=q['positive_zero_bijection_proved'],source_sha256=srcsha))
   if extra==0 or sh==(-1,-1,-1,-1):selected.append(q)
  need(dict(hist)=={74:4,75:20,76:33,77:20,78:4},'independent finite cost histogram');histograms[p['mode']]={str(k):v for k,v in sorted(hist.items())}
 need(seen==expected and len(census)==243,'complete independent finite recipe set')
 # Mask-only shift obstruction, including the pretyping interval proof premises.
 # Native MF is MF_source-(B-1). These bounds require only q=(B-1)J+1,
 # not q being a power or a successfully typed history.
 masks=0
 for B in(16,32,64):
  for J in(1,2,3,7):
   q=(B-1)*J+1
   for MC,MF in((2,4),(B-2,B-2)):
    tc=MC*J+1;tf=MF*J-1;tp=tc+q*tf
    need(0<tc<q and 0<tf<q and 0<tp<q*q-1,'pretyping nonzero remainder bound')
    need((MC+q*(MF+B-1))*J-(q*q-1)==tp,'actual shifted MF remainder identity')
    for dmc,dmf in itertools.product((-3,-1,0,1,3),repeat=2):need(((dmc+q*dmf)*J)%J==0,'fixed mask changes divisible by J');masks+=1
 return dict(schema='complete74-index-transport-affine-scout-v1',source_sha256=sha(Path(__file__).read_bytes()),parent_pins=PINS,scope={'recipe_ports':list(PORTS),'shifts':[-1,0,1],'recipes_per_mode':81,'complete_sources_checked':243,'selected_complete_sources_saved':len(selected),'no_global_optimality_claim':True,'no_improvement_found':True,'historical_modules_imported':False,'positive_zero_bijections_proved':12,'domain_for_other_recipes':'all-value ring pullback only; no positive-zero equivalence asserted'},local_coefficient_proof=local,counts=dict(sorted(totals.items())),cost_histograms=histograms,actual_parent_consumers=privacy,mask_arithmetic_checks=masks,census=census,selected_complete_sources=selected)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--output');ap.add_argument('--expect');args=ap.parse_args();result=verify(args.root)
 if args.expect:need(exact(result,json.loads(Path(args.expect).read_text())),'exact typed saved receipt')
 if args.output:Path(args.output).write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':'PASS','counts':result['counts'],'best_certificate':74,'selected_sources':len(result['selected_complete_sources'])},sort_keys=True))
if __name__=='__main__':main()
