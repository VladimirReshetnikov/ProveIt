#!/usr/bin/env python3
"""Five signed registers and a paid97-choice countdown transition for directed193."""
import argparse
from fractions import Fraction
import hashlib
from itertools import product
import json
from pathlib import Path

NEW_PINS={
 'matrix193_synchronized_rows.py':'da55246efc8047b6b3f188579cf6c71bbabb067def3fe04ac47ba61b56517e52',
 'matrix193_synchronized_rows.json':'9ce8537fc12bff3a2d3d91297d65a47ee6a7af193ff4bb08f474216260ef4233',
 'matrix193_synchronized_rows.md':'ab768aa392841add5dc6dfcd8ed62564ca17fae2fe80e5ec39f1f4ceb36559d2',
 'matrix195_counted_suffix.py':'bb876b65fa0544a8f8174e09a493715e47501a850ff518a2daed0643ead65b67',
 'matrix195_counted_suffix.json':'3c803a9a219eebf299a40dcece8958e905b3c59f8ba8b5cb1e60d9c52812c5bd',
 'matrix195_counted_suffix.md':'f53c2af29b0f3f292a047e9b16d29a94cd634ebd0337391bd8159beda63ca307'}
PINS={
 'matrix193_context_absorption.json':'73f8cae212c6c1917e73cc76c7bf3c43b8c587748bbf4327eddf4c82e726a436',
 'matrix193_context_absorption.md':'d7492809ba00a011c8280172bb016f96f3f6c240de6a823ed717d82bda5e4f4b'}
BASE=['x0','x1','y0','y1','next_x0','next_x1','next_y0','next_y1'];PORTS=BASE+['n','next_n']
I=[1,0,0,1]
def need(p,s):
 if not p:raise ValueError(s)
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
def matmul(a,b):return [a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3]]
def inverse(a):
 need(a[0]*a[3]-a[1]*a[2]==1,'SL2 inverse');return [a[3],-a[1],-a[2],a[0]]
def upper(m):return [m[0][0],m[0][1],m[1][0],m[1][1]]
def act(v,M):return [v[0]*M[0]+v[1]*M[2],v[0]*M[1]+v[1]*M[3]]
class Builder:
 def __init__(self,prefix):
  self.rows=[r[:] for r in prefix];self.memo={(r[1],r[2],r[3]):r[0] for r in prefix}
 def gate(self,op,a,b):
  if op in ('+','*') and repr(a)>repr(b):a,b=b,a
  key=op,a,b
  if key in self.memo:return self.memo[key]
  n='g'+str(len(self.rows));self.rows.append([n,op,a,b]);self.memo[key]=n;return n
 def square(self,a):return self.gate('*',a,a)
 def total(self,a):
  r=a[0]
  for t in a[1:]:r=self.gate('+',r,t)
  return r

def emit(old,Bi):
 b=Builder(old['instructions']);load=[]
 for k in (0,1):load.append(b.gate('-',BASE[4+k],BASE[k]))
 for k in (0,1):
  pred=b.gate('+',b.gate('*',Bi[k],'y0'),b.gate('*',Bi[k+2],'y1'))
  load.append(b.gate('-',BASE[6+k],pred))
 load.append(b.gate('-',b.gate('-','n','next_n'),1))
 loader=b.total([b.square(r) for r in load]);tile=b.total([old['output'],b.square('n'),b.square('next_n')]);out=b.gate('*',loader,tile)
 M=sum(r[1]=='*' for r in b.rows)
 ep=Builder([]);r0=ep.gate('-','x0','y0');r1=ep.gate('-','x1','y1');end=ep.total([ep.square(r0),ep.square(r1),ep.square('n')])
 return {'ports':PORTS,'instructions':b.rows,'output':out,'loader_residuals':load,'loader_factor':loader,'tile_factor':tile,'parent_output':old['output'],
  'ledger':{'M':M,'A':len(b.rows)-M,'total':len(b.rows)},'exact_degree':194,
  'endpoint':{'ports':['x0','x1','y0','y1','n'],'instructions':ep.rows,'output':end,'ledger':{'M':3,'A':4,'total':7}},
  'domain':'ten signed supplied state coordinates; no auxiliary selector/phase/Pell coordinates'}
def evaluate(p,z):
 v=dict(zip(p['ports'],z))
 def get(a):return a if type(a) is int else v[a]
 for n,o,a,b in p['instructions']:
  x,y=get(a),get(b);v[n]=x+y if o=='+' else x-y if o=='-' else x*y
 return v[p['output']]
def padd(a,b,s=1):
 d=dict(a)
 for k,v in b.items():
  d[k]=d.get(k,0)+s*v
  if not d[k]:del d[k]
 return d
def pmul(a,b):
 d={}
 for i,x in a.items():
  for j,y in b.items():d[i+j]=d.get(i+j,0)+x*y
 return {i:x for i,x in d.items() if x}
def source_audit(p,old,Bi):
 need(p['instructions'][:len(old['instructions'])]==old['instructions'],'full exact parent prefix')
 known=set(p['ports']);degrees={v:1 for v in known};line={v:({1:1} if v=='next_x0' else {}) for v in known};seen={}
 for row in p['instructions']:
  n,op,a,b=row;need(n not in known and op in ('+','-','*'),'fresh wellformed gate')
  for r in (a,b):need(type(r) is int or r in known,'source closure')
  da=0 if type(a) is int else degrees[a];db=0 if type(b) is int else degrees[b]
  degrees[n]=da+db if op=='*' else max(da,db)
  pa=({0:a} if a else {}) if type(a) is int else line[a];pb=({0:b} if b else {}) if type(b) is int else line[b]
  line[n]=pmul(pa,pb) if op=='*' else padd(pa,pb,1 if op=='+' else -1)
  known.add(n);seen[n]=row
 need(degrees[p['output']]==194 and line[p['output']]=={194:1,192:1},'uniform exact194 line certificate')
 live=set()
 def visit(n):
  if type(n) is int or n in live or n not in seen:return
  live.add(n);visit(seen[n][2]);visit(seen[n][3])
 visit(p['output']);need(len(live)==len(seen),'full source liveness')
 # Independently interpret only the added DAG over a formal parent-output port.
 # Its operations are compared as polynomials with the direct grouped formula.
 names=PORTS+['parent'];zero=(0,)*len(names)
 def const(c):return {zero:c} if c else {}
 ring={v:{tuple(int(i==j) for i in range(len(names))):1} for j,v in enumerate(names)}
 ring[old['output']]=ring['parent']
 def add(a,b,s=1):return padd(a,b,s)
 def multiply(a,b):
  d={}
  for m,x in a.items():
   for n,y in b.items():
    z=tuple(i+j for i,j in zip(m,n));d[z]=d.get(z,0)+x*y
  return {m:x for m,x in d.items() if x}
 for n,op,a,b in p['instructions'][len(old['instructions']):]:
  pa=const(a) if type(a) is int else ring[a];pb=const(b) if type(b) is int else ring[b]
  ring[n]=multiply(pa,pb) if op=='*' else add(pa,pb,1 if op=='+' else -1)
 loader={}
 residual=[]
 for a,b in (('next_x0','x0'),('next_x1','x1')):residual.append(add(ring[a],ring[b],-1))
 for k in (0,1):residual.append(add(add(ring[BASE[6+k]],multiply(const(Bi[k]),ring['y0']),-1),multiply(const(Bi[k+2]),ring['y1']),-1))
 residual.append(add(add(ring['n'],ring['next_n'],-1),const(1),-1))
 for r in residual:loader=add(loader,multiply(r,r))
 tile=add(add(ring['parent'],multiply(ring['n'],ring['n'])),multiply(ring['next_n'],ring['next_n']))
 need(ring[p['loader_factor']]==loader and ring[p['tile_factor']]==tile and ring[p['output']]==multiply(loader,tile),'complete formal parent-cut identity')
 return len(ring[p['output']])
def digest_state(h,s):
 for z in s:
  b=abs(z).to_bytes(max(1,(abs(z).bit_length()+7)//8),'big');h.update(bytes([z<0]));h.update(len(b).to_bytes(8,'big'));h.update(b)

def verify(root,newroot):
 raw={}
 for base,pins in ((root,PINS),(newroot,NEW_PINS)):
  for name,h in pins.items():
   b=(base/name).read_bytes();need(sha(b)==h,'pin '+name);raw[name]=b
 old=loads(raw['matrix193_synchronized_rows.json']);ctx=loads(raw['matrix193_context_absorption.json']);count=loads(raw['matrix195_counted_suffix.json'])
 need(old['source_sha256']==NEW_PINS['matrix193_synchronized_rows.py'] and count['source_sha256']==NEW_PINS['matrix195_counted_suffix.py'],'parent self hashes')
 table=old['transition_table'];B=ctx['block']['B'];Bi=inverse(B);p=emit(old['packet'],Bi);terms=source_audit(p,old['packet'],Bi)
 gens={r['name']:r['matrix'] for r in ctx['packet']['generators']};C=upper(gens['C']);Ci=inverse(C)
 for t in table:
  need(t['H']==upper(gens['A'+str(t['tile_id'])]) and t['G']==inverse(upper(gens['B'+str(t['tile_id'])])),'actual phase pairs')
  need(t['K']==matmul(matmul(Ci,t['H']),C),'actual synchronized conjugacy')
 byid={t['tile_id']:t for t in table};traces=[];total_steps=0;actual_full_source=0
 for w in count['accepting_witnesses']:
  x=w['x'];seq=w['tileword'];need(type(x) is int and x>=0,'ordinary natural fixture')
  need(w['parent_word']==['A'+str(i) for i in seq]+['C']+['B'+str(i) for i in seq[::-1]],'actual shaped parent word')
  X=C[:2];Y=[1,0];n=x;h=hashlib.sha256();digest_state(h,X+Y+[n]);maxbits=max(abs(v).bit_length() for v in X+Y+[n]);M=I
  for load_index in range(x):
   nxt=act(Y,Bi);M=matmul(M,Bi);need(nxt==M[:2],'loader full matrix identity')
   if load_index==0:
    need(evaluate(p,X+Y+X+nxt+[n,n-1])==0,'selected actual full loader source');actual_full_source+=1
   Y=nxt;n-=1;digest_state(h,X+Y+[n]);total_steps+=1
  need(n==0,'exact ordinary count')
  Htot=I;Gtot=I
  for step_index,i in enumerate(seq):
   t=byid[i];before=X+Y;X=act(X,t['K']);Y=act(Y,t['G']);Htot=matmul(Htot,t['H']);Gtot=matmul(Gtot,t['G'])
   if step_index in (0,len(seq)-1):
    need(evaluate(p,before+X+Y+[n,n])==0,'selected actual full tile source');actual_full_source+=1
   need(X==matmul(Htot,C)[:2] and Y==matmul(M,Gtot)[:2],'whole trajectory matrix induction')
   maxbits=max(maxbits,*(abs(v).bit_length() for v in X+Y));digest_state(h,X+Y+[n]);total_steps+=1
  need(X==Y and matmul(matmul(Htot,C),inverse(Gtot))==M,'actual positive-input accepted endpoint')
  need(evaluate(p['endpoint'],X+Y+[n])==0,'paid endpoint zero')
  traces.append({'x':x,'tile_sequence':seq,'loader_steps':x,'tile_steps':len(seq),'total_steps':x+len(seq),'input_word':w['input_word'],'trajectory_sha256':h.hexdigest(),'maximum_row_magnitude_bits':maxbits,'endpoint_equal':True})
 # Abstract control check permits signed counters and zero tile count.
 controls=0
 for x in range(-2,5):
  for size in range(11):
   for word in product('LT',repeat=size):
    n=x;valid=True
    for a in word:
     if a=='L':n-=1
     elif n!=0:valid=False;break
    accepts=valid and n==0
    expected=x>=0 and len(word)>=x and word==tuple('L'*x+'T'*(len(word)-x))
    need(accepts==expected,'signed control language');controls+=1
 # Complete polynomial evaluations are bounded; large traces use the already
 # proved branch identities instead of expanding enormous off-branch factors.
 zeros=0
 for j,t in enumerate(table):
  X=[j-50,j+3];Y=[-j-7,2*j+1];n=0
  z=X+Y+act(X,t['K'])+act(Y,t['G'])+[n,n]
  need(evaluate(p,z)==0,'all tile branch local zeros');zeros+=1
 for n in (-3,0,1,7):
  X=[3,-2];Y=[-4,7];need(evaluate(p,X+Y+X+act(Y,Bi)+[n,n-1])==0,'signed loader branch zero');zeros+=1
 arbitrary=0;rational=0
 for k in range(16):
  z=[Fraction((k+7)*(j+3)%23-11,5 if k%3==0 else 1) for j in range(10)]
  xp,yp=z[4:6],z[6:8];prediction=act(z[2:4],Bi)
  E=sum((xp[i]-z[i])**2 for i in range(2))+sum((yp[i]-prediction[i])**2 for i in range(2))+(z[8]-z[9]-1)**2
  F=evaluate(old['packet'],z[:8])+z[8]**2+z[9]**2
  need(evaluate(p,z)==E*F,'whole signed/rational grouped identity');arbitrary+=1;rational+=int(k%3==0)
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'pins':dict(PINS,**NEW_PINS),
  'packet':p,'transitions':{'loader':{'X':'unchanged','Y_matrix':Bi,'counter_change':-1},'tiles':table,'tile_counter_guard':'n=next_n=0','count':97},
  'initial_state':{'X':C[:2],'Y':[1,0],'n':'ordinary_x','instructions':[],'operations':0},
  'accepting_traces':traces,'checks':{'actual_tile_pairs':96,'formal_grouped_coefficient_entries':terms,'control_words':controls,'actual_trajectory_steps':total_steps,'selected_actual_full_source_zeros':actual_full_source,'bounded_full_local_zeros':zeros,'whole_arbitrary_evaluations':arbitrary,'rational_evaluations':rational,'exact_degree_line':{'194':1,'192':1}},
  'scope':'Exact five-register countdown orbit for fixed-program directed193, with ordinary integer input copied directly. Complete97-choice local polynomial and endpoint are paid; arbitrary-length bounded-variable history encoding is not.',
  'external_Pell_index_relation_required':False,'unbounded_history_Diophantine_certificate_paid':False,'new_universal_Diophantine_bound':False,'predecessor_code_executed':False}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',required=True,type=Path);ap.add_argument('--new-root',type=Path)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--expect',type=Path);g.add_argument('--output',type=Path)
 ns=ap.parse_args();out=verify(ns.root,ns.new_root or ns.root)
 if ns.expect:need(exact(out,loads(ns.expect.read_bytes())),'type-exact receipt')
 else:ns.output.write_text(json.dumps(out,sort_keys=True,indent=2,allow_nan=False)+'\n')
 print('PASS: five-register ordinary-input countdown;',out['packet']['ledger'],'degree194; four accepted traces')
if __name__=='__main__':main()
