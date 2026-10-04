#!/usr/bin/env python3
"""Exact synchronized four-row-coordinate preprocessing of the saved193 relation."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

PINS={
 'matrix193_context_absorption.py':'1304ea242ca6a5faafdb527ac3e56c6cd06b0276dca6441fc3477c7065054485',
 'matrix193_context_absorption.json':'73f8cae212c6c1917e73cc76c7bf3c43b8c587748bbf4327eddf4c82e726a436',
 'matrix193_context_absorption.md':'d7492809ba00a011c8280172bb016f96f3f6c240de6a823ed717d82bda5e4f4b',
 'matrix193_gamma1_recode.md':'6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742',
 'group_directed_semigroup193.md':'75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e'}
PORTS=['x0','x1','y0','y1','next_x0','next_x1','next_y0','next_y1']
I=[1,0,0,1]
def need(b,s):
 if not b:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def pairs(xs):
 d={}
 for k,v in xs:
  need(k not in d,'duplicate JSON key');d[k]=v
 return d
def loads(b):return json.loads(b,object_pairs_hook=pairs,parse_constant=lambda x:(_ for _ in ()).throw(ValueError(x)))
def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def mul(a,b):return [a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3]]
def inv(a):
 need(a[0]*a[3]-a[1]*a[2]==1,'SL2 inverse')
 return [a[3],-a[1],-a[2],a[0]]
def row(v,a):return [v[0]*a[0]+v[1]*a[2],v[0]*a[1]+v[1]*a[3]]
def upper(a):return [a[0][0],a[0][1],a[1][0],a[1][1]]
def mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(4)) for j in range(4)] for i in range(4)]

class Builder:
 def __init__(self):self.rows=[];self.memo={}
 def gate(self,op,a,b):
  if type(a) is int and type(b) is int:return a+b if op=='+' else a-b if op=='-' else a*b
  if op=='*':
   if a==0 or b==0:return 0
   if a==1:return b
   if b==1:return a
  if op=='+':
   if a==0:return b
   if b==0:return a
  if op=='-' and b==0:return a
  if op in ('+','*') and repr(a)>repr(b):a,b=b,a
  key=(op,a,b)
  if key in self.memo:return self.memo[key]
  n='g'+str(len(self.rows));self.rows.append([n,op,a,b]);self.memo[key]=n;return n
 def linear(self,x,y,a,c):return self.gate('+',self.gate('*',a,x),self.gate('*',c,y))
 def summation(self,z):
  out=z[0]
  for t in z[1:]:out=self.gate('+',out,t)
  return out

def emit(table):
 b=Builder();branches=[]
 for t in table:
  K,G=t['K'],t['G'];pred=[]
  for base,M in ((0,K),(2,G)):
   pred.extend([b.linear(PORTS[base],PORTS[base+1],M[j],M[j+2]) for j in (0,1)])
  residual=[b.gate('-',PORTS[4+j],p) for j,p in enumerate(pred)]
  factor=b.summation([b.gate('*',r,r) for r in residual])
  branches.append({'tile_id':t['tile_id'],'predictions':pred,'residuals':residual,'factor':factor})
 split=len(b.rows);out=branches[0]['factor']
 for t in branches[1:]:out=b.gate('*',out,t['factor'])
 live=set()
 producers={r[0]:r for r in b.rows}
 def visit(x):
  if isinstance(x,str) and x in live:return
  if isinstance(x,str) and x in producers:
   live.add(x);visit(producers[x][2]);visit(producers[x][3])
 visit(out);need(len(live)==len(b.rows),'whole source liveness')
 muls=sum(r[1]=='*' for r in b.rows)
 return {'ports':PORTS,'instructions':b.rows,'branches':branches,'product_start':split,'output':out,'ledger':{'M':muls,'A':len(b.rows)-muls,'total':len(b.rows)},'exact_degree':192,'witnesses_for_one_step':0,'domain':'eight signed supplied coordinates'}

def evaluate(packet,values):
 v=dict(zip(PORTS,values))
 def get(z):return z if type(z) is int else v[z]
 for n,op,a,b in packet['instructions']:
  x,y=get(a),get(b);v[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return v[packet['output']]

def polyadd(a,b,s=1):
 c=dict(a)
 for m,k in b.items():
  c[m]=c.get(m,0)+s*k
  if not c[m]:del c[m]
 return c
def polymul(a,b):
 c={}
 for m,x in a.items():
  for n,y in b.items():
   z=tuple(i+j for i,j in zip(m,n));c[z]=c.get(z,0)+x*y
 return {m:x for m,x in c.items() if x}
def coefficients(packet,table):
 zero=(0,)*8;v={p:{tuple(int(j==k) for j in range(8)):1} for k,p in enumerate(PORTS)}
 def get(x):return {zero:x} if type(x) is int and x else {} if type(x) is int else v[x]
 for n,op,a,b in packet['instructions'][:packet['product_start']]:
  x,y=get(a),get(b);v[n]=polyadd(x,y) if op=='+' else polyadd(x,y,-1) if op=='-' else polymul(x,y)
 count=0
 for t,b in zip(table,packet['branches']):
  expected={}
  for j,M in enumerate((t['K'],t['G'])):
   for k in (0,1):
    weights={4+2*j+k:1,2*j:-M[k],2*j+1:-M[k+2]}
    f={tuple(int(q==i) for q in range(8)):a for i,a in weights.items() if a}
    need(v[b['residuals'][2*j+k]]==f,'independent literal residual coefficients')
    expected=polyadd(expected,polymul(f,f))
  need(v[b['factor']]==expected,'independent complete branch coefficients');count+=len(expected)
 factors=[b['factor'] for b in packet['branches']];acc=factors[0]
 for r,f in zip(packet['instructions'][packet['product_start']:],factors[1:]):
  need(r[1]=='*' and set(r[2:])=={acc,f},'complete union product closure');acc=r[0]
 need(acc==packet['output'] and len(packet['instructions'])-packet['product_start']==95,'all 96 factors paid')
 return count

def verify(root):
 data={}
 for name,h in PINS.items():
  raw=(root/name).read_bytes();need(sha(raw)==h,'pin '+name);data[name]=raw
 parent=loads(data['matrix193_context_absorption.json']);need(parent['source_sha256']==PINS['matrix193_context_absorption.py'],'parent self hash')
 gens={r['name']:r['matrix'] for r in parent['packet']['generators']};C=upper(gens['C']);Ci=inv(C)
 ids=sorted(r['tile_id'] for r in parent['packet']['generators'] if r['name'].startswith('A'))
 need(len(ids)==96 and len(gens)==193,'complete actual table')
 table=[]
 for i in ids:
  H=upper(gens['A'+str(i)]);G=inv(upper(gens['B'+str(i)]));K=mul(mul(Ci,H),C)
  need(mul(C,K)==mul(H,C),'local conjugate transfer')
  inv(K);inv(G);table.append({'tile_id':i,'H':H,'G':G,'K':K})
 need(len({tuple(t['K']+t['G']) for t in table})==96,'distinct transition pairs')
 packet=emit(table);count=coefficients(packet,table)
 byid={t['tile_id']:t for t in table}
 witness=parent['accepting_witness'];word=witness['generator_word'];pos=word.index('C');seq=[int(n[1:]) for n in word[:pos]]
 need(word==['A'+str(i) for i in seq]+['C']+['B'+str(i) for i in seq[::-1]],'actual lower-forced word shape')
 M=upper(witness['target']);x=C[:2];y=M[:2];Htot=I;Gtot=I;trajectory=[{'x':x,'y':y}]
 for i in seq:
  t=byid[i];nx=row(x,t['K']);ny=row(y,t['G']);need(evaluate(packet,x+y+nx+ny)==0,'accepted local transition zero')
  Htot=mul(Htot,t['H']);Gtot=mul(Gtot,t['G'])
  need(nx==mul(Htot,C)[:2] and ny==mul(M,Gtot)[:2],'complete matrix induction')
  x,y=nx,ny;trajectory.append({'x':x,'y':y})
 need(x==y and mul(mul(Htot,C),inv(Gtot))==M,'actual final row/matrix equality')
 prod=[[int(i==j) for j in range(4)] for i in range(4)]
 for name in word:prod=mm(prod,gens[name])
 need(prod==witness['target'],'full 167 factor matrix product')
 # Every branch gets a separate signed row fixture, rather than only the used tiles.
 transition_checks=0
 for ix,t in enumerate(table):
  x=[ix-49,3-ix];y=[2*ix+1,-ix-7];nx=row(x,t['K']);ny=row(y,t['G'])
  need(evaluate(packet,x+y+nx+ny)==0,'all finite branch zero fixtures');transition_checks+=1
 arbitrary=0;rational=0
 for k in range(16):
  z=[Fraction((k+3)*(j+5)%19-9,3 if k%3==0 else 1) for j in range(8)];expected=1
  for t in table:
   p=row(z[:2],t['K'])+row(z[2:4],t['G']);expected*=sum((z[4+j]-p[j])**2 for j in range(4))
  need(evaluate(packet,z)==expected,'whole signed/rational product evaluation');arbitrary+=1;rational+=int(k%3==0)
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'transition_table':table,'packet':packet,
  'initial_first_row':C[:2],'endpoint_polynomial':{'expression':'(x0-y0)^2+(x1-y1)^2','M':2,'A':3,'total':5},
  'accepting_fixture':{'ordinary_parameter':witness['ordinary_parameter'],'tile_sequence':seq,'trajectory':trajectory,'product':prod},
  'checks':{'local_conjugate_identities':96,'independent_linear_residuals':384,'independent_quadratic_coefficients':count,'all_tile_zeros':transition_checks,'accepted_transition_zeros':len(seq),'accepted_generator_factors':len(word),'whole_arbitrary_checks':arbitrary,'rational_checks':rational},
  'scope':'Exact unbounded relation transfer to synchronized signed four-coordinate orbit; complete paid one-step polynomial only. Fixed-variable unbounded history packing and ordinary-input indexing remain unpaid.',
  'unbounded_history_Diophantine_certificate_paid':False,'new_universal_Diophantine_bound':False,'predecessor_code_executed':False}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',required=True,type=Path)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--expect',type=Path);g.add_argument('--output',type=Path)
 ns=ap.parse_args();out=verify(ns.root)
 if ns.expect:need(exact(out,loads(ns.expect.read_bytes())),'type-exact receipt')
 else:ns.output.write_text(json.dumps(out,sort_keys=True,indent=2,allow_nan=False)+'\n')
 print('PASS: 193 matrices to 96 synchronized transitions; local paid source',out['packet']['ledger'])
if __name__=='__main__':main()
