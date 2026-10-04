#!/usr/bin/env python3
"""Freshly reconstructed independent observer; no old implementation-byte claim.
Only the newly reconstructed merged generator is executed; frozen assets are DATA.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from array import array
from collections import Counter
import os,json,hashlib,importlib.util
ROOT=Path(os.environ.get('ANT_CERTIFICATE_ROOT','/workspace/shared/complete-ant-certificate-recovered-20261004-v2')).resolve()
HERE=Path(__file__).resolve().parent
U,V,X0=481238074400,576000,481225262775
P=1000000007
OLD={2:'c16901162e09b07d1e0c27b28e29dcc12a9b6137391fce85e3f150a3fed37eac',1:'85a161972769207e4f5d4212214630535208f69d6736bca2b46a8aff8276a22a'}
SPECIAL={'Cu':pow(3,U,P),'Cx':(pow(3,U,P)-1)%P,'Cbase':pow(3,U-219,P),'C198':pow(3,198,P),'EndpointK':pow(3,X0,P),'EndpointD':(pow(3,U,P)-2)%P}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def read(name):return json.loads((ROOT/name).read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def sample(s):return int.from_bytes(hashlib.sha256(s.encode()).digest()[:8],'big')%P
def constant(s):
 k=s[2:]
 if k.lstrip('-').isdigit():
  need(int(k) in [0,1,2,3,4,6,8,9],'unpaid small coefficient');return int(k)%P
 if k in SPECIAL:return SPECIAL[k]
 typ,num=k.split(':');j=int(num)
 need(typ in ['tile','first','anchor'] and 0<=j<(584 if typ=='anchor' else V),'unknown coefficient')
 return sample(s) # Independent test specialization, not physical coefficient evaluation.
class Observer:
 def __init__(self,arity):
  self.arity=arity;self.names={};self.witness=[];self.deg=array('I');self.val=array('I');self.count=Counter();self.eq=[];self.raw=None;self.final=None;self.hash=hashlib.sha256();self.constants=set();self.sectionends={}
 def value(self,x):
  if type(x)is int:
   need(0<=x<len(self.val),'non-topological reference');return self.val[x]
  need(type(x)is str,'operand type')
  if x.startswith('C:'):self.constants.add(x);return constant(x)
  need(x in self.names,'undeclared variable');return self.names[x]
 def degree(self,x):return self.deg[x] if type(x)is int else (0 if x.startswith('C:') else 1)
 def write(self,line):
  need(self.final is None,'event after final assertion');self.hash.update(line.encode());r=json.loads(line)
  if r[0]=='raw_positive':
   need(self.raw is None and not self.val,'raw declaration order');self.raw=r[1]
   need(self.raw==(['RawLeft','RawRight'] if self.arity==2 else ['RawInput']),'raw domain')
   for x in self.raw:self.names[x]=sample(x)
  elif r[0]=='positive':
   x=r[1];need(x not in self.names and not x.startswith('C:'),'duplicate witness');self.names[x]=sample(x);self.witness.append(x)
  elif r[0]=='residual_pair':
   _,i,a,b,section=r;need(i==len(self.eq),'residual index');av,bv=self.value(a),self.value(b)
   self.eq.append((section,(av-bv)%P,max(self.degree(a),self.degree(b)),a,b));self.sectionends[section]={'end':len(self.val),'cumulative_operations':dict(self.count)}
  elif r[0]=='eq':
   need(r[2]=='C:0','final assertion');self.final=(r[1],self.value(r[1]),self.value(r[2]),self.degree(r[1]))
  else:
   i,op,a,b=r;need(type(i)is int and i==len(self.val) and op in ['+','-','*'],'gate schema')
   av,bv=self.value(a),self.value(b);ad,bd=self.degree(a),self.degree(b)
   self.val.append((av+bv if op=='+' else av-bv if op=='-' else av*bv)%P);self.deg.append(ad+bd if op=='*' else max(ad,bd));self.count[op]+=1
  return len(line)
def eval_json(data,env):
 env=dict(env)
 def v(x):return x%P if type(x)is int else env[x]
 for out,op,a,b in data['nodes']:
  need(out not in env,'JSON register collision');a,b=v(a),v(b);env[out]=(a+b if op=='+' else a-b if op=='-' else a*b)%P
 return env,[(v(a)-v(b))%P for a,b in data.get('equations',data.get('equalities',[]))]
def residual_reference(o):
 n=o.names;h=read('history/history174.json');pars=['InitialMemoryPlus','FinalMemoryPlus','InitialHead','FinalHead','FinalSignPlus']
 env={x:n['Parent:'+x] for x in pars};env.update({x:n['History:'+x] for x in h['witnesses']});_,history=eval_json(h,env)
 pair=read('data/pair_inline-dag.json');W=n['History:W'];Wp=n['History:Wp'];Q=n['History:Q'];G=pow(W,V,P)
 env={'G':G,'RawLeft':n['RawLeft'],'RawRight':n['RawRight']};env.update({x:n['Init:Recoder:'+x] for x in pair['witnesses']});e,pairres=eval_json(pair,env);A,B,T=(e[pair['outputs'][k]] for k in ['A','B','T'])
 H=n['Init:HalfRowsPower'];K=n['Init:HalfPeriodRepunit'];Pad=n['Init:PaddingPower'];hx=n['Init:HorizontalExtra']+1
 def horner(cat,size):
  a=0
  for j in range(size-1,-1,-1):a=(a*W+constant('C:'+cat+':'+str(j)))%P
  return a
 tile,first,anchor=horner('tile',V),horner('first',V),horner('anchor',584)
 bg=K*(H+1)*(hx*tile+Wp*first)
 patch=constant('C:Cbase')*Pad*(pow(W,V-550,P)*A*anchor-constant('C:C198')*(W+1)*(pow(W,23945,P)+pow(W,263945,P)*(pow(W,264000,P)+1)*(pow(W,24000,P)*T+B)))
 init=[Wp-1-constant('C:Cx')*hx,H-1-(G-1)*K,Q-H*H]+pairres+[H-Pad*A*G,n['Parent:InitialHead']-constant('C:Cu')*H,n['Parent:InitialMemoryPlus']-bg-patch-1]
 col=constant('C:EndpointK')*(constant('C:Cx')*n['Endpoint:HxPlus']-constant('C:EndpointD'))
 endpoint=[col+n['Endpoint:BoundCol']-W,col*pow(W,29948,P)*(1+(G-1)*(n['Endpoint:HyPlus']-1))-n['Parent:FinalHead'],n['Parent:FinalSignPlus']-1]
 want=[x%P for x in history+init+endpoint]
 if o.arity==1:
  x,y,N=(n[k] for k in ['RawLeft','RawRight','RawInput']);want.append((2*N-(x+y-2)*(x+y-1)-2*y)%P)
 need([x[1] for x in o.eq]==want,'independent component identity regression')
 need(o.final[1]==sum(x*x for x in want)%P and o.final[2]==0,'independent SOS regression')
def run(arity,m):
 o=Observer(arity);reported=m.build(o,arity);residual_reference(o)
 expected=(['RawLeft','RawRight'] if arity==1 else [])+['Parent:'+x for x in ['InitialMemoryPlus','FinalMemoryPlus','InitialHead','FinalHead','FinalSignPlus']]+['History:'+x for x in read('history/history174.json')['witnesses']]+['Init:'+x for x in ['HorizontalExtra','HalfRowsPower','HalfPeriodRepunit','PaddingPower']]+['Init:Recoder:'+x for x in read('data/pair_inline-dag.json')['witnesses']]+['Endpoint:'+x for x in ['HxPlus','HyPlus','BoundCol']]
 need(o.witness==expected,'complete positive-coordinate ledger')
 M=o.count['*'];A=o.count['+']+o.count['-'];need((M,A,len(o.val))==((1153586,1153871,2307457) if arity==2 else (1153590,1153877,2307467)),'operation ledger')
 need(len(o.eq)==285+(arity==1) and len(o.witness)==465+2*(arity==1),'equation/witness ledger')
 top=[i for i,x in enumerate(o.eq) if x[2]==1152000];need(top==[64,178],'maximal residuals');need(max(x[2] for x in o.eq if x[2]<1152000)==1127949,'other bound');need(o.final[3]==2304000,'final degree upper bound')
 receipt=read(('two' if arity==2 else 'one')+'-input-receipt.json')
 need(o.hash.hexdigest()==OLD[arity]==reported['source_sha256']==receipt['source_sha256'],'actual complete canonical stream hash')
 coeffs={'C:'+str(x) for x in [0,1,2,3,4,6,8,9]}|{'C:'+x for x in SPECIAL}|{'C:'+cat+':'+str(j) for cat,size in [('tile',V),('first',V),('anchor',584)] for j in range(size)}
 need(o.constants==coeffs,'exact coefficient closure')
 return {'arity':arity,'M':M,'A':A,'operations':len(o.val),'positive_witnesses':len(o.witness),'stored_residuals':len(o.eq),'asserted_equations':1,'canonical_stream_sha256':o.hash.hexdigest(),'historical_stream_identity_verified':True,'coefficient_labels':len(coeffs),'top_residuals':top,'other_residual_upper_bound':1127949,'exact_degree_by_source_proof':2304000,'leading_homogeneous_part':'2*History:W^2304000','off_solution_checks':len(o.eq),'modulus':P,'section_ends':o.sectionends}
def bounded():
 seen=set()
 for n in range(101):
  block=[]
  for y in range(1,n+2):
   x=n+2-y;N=((x+y-2)*(x+y-1)+2*y)//2;need(N not in seen and 2*N==(x+y-2)*(x+y-1)+2*y,'pair bijection');seen.add(N);block.append(N)
  need(block==list(range(n*(n+1)//2+1,(n+1)*(n+2)//2+1)),'pair interval')
 need(seen==set(range(1,5152)),'pair coverage');tests=accepted=geometry=0
 for u in [2,4,6]:
  for v in [2,4]:
   for x0 in range(1,u,2):
    for y0 in range(0,v,2):
     for w in [u+1,2*u+1,3*u+1]:
      for h in [2*v,4*v]:
       W=3**w;K=3**x0;C=3**u-1;D=C-1;G=W**v
       for x in range(w):
        for y in range(h):
         tests+=1;want=x%u==x0 and y%v==y0;candidate=x>=x0 and y>=y0 and (3**(x-x0)-1)%C==0 and (W**(y-y0)-1)%(G-1)==0;need(candidate==want,'endpoint iff')
         if candidate:
          hx=(3**(x-x0)-1)//C+1;hy=(W**(y-y0)-1)//(G-1)+1;col=K*(C*hx-D);bound=W-col;need(min(hx,hy,bound)>0 and col*W**y0*(1+(G-1)*(hy-1))==3**(x+w*y),'endpoint converse');accepted+=1
   for a in [2,3]:
    for n in range(4):
     for k in range(n+1,n+4):
      w=1+a*u;W=3**w;G=W**v;H=G**k;X=(3**(a*u)-1)//(3**u-1)-1;K=(H-1)//(G-1);Pad=G**(k-n-1)
      need(min(X,H,K,Pad)>0 and 3**(w-1)-1==(3**u-1)*(X+1) and H-1==(G-1)*K and H==Pad*G**(n+1),'initializer geometry');geometry+=1
 return {'pair_values':len(seen),'endpoint_sites':tests,'endpoint_accepting_sites':accepted,'initial_geometry_cases':geometry,'physical_ant_simulation':False}
def strict():
 L=lambda n:n.bit_length()+n.bit_count()-2 if n>1 else 0
 m=V*(U-1)+584*220+L(U)+L(U-219)+L(198)+L(X0)+1;a=V*(U-1)+584*220+8
 need((m,a)==(277193130853952643,277193130853952488),'strict prefix')
 return {'M':m,'A':a,'total':m+a,'two_input_total':m+a+2307457,'one_input_total':m+a+2307467,'chain_lengths':{str(x):L(x) for x in [U,U-219,198,X0,V]}}
def main():
 verified=[];optional_missing=[]
 for rel,meta in read('history/SOURCE_PINS.json').items():
  p=Path(meta['path']) if rel.startswith('external/') else ROOT/'history'/rel
  if rel.startswith('external/') and not p.exists():optional_missing.append(str(p));continue
  need(sha(p)==meta['sha256'],'history source pin '+rel);verified.append(rel)
 expected={'history/history174.json':'2075bb290f3f81d7c04a27b82f50c4f492638d55a3a27f434f66497ae9fb90ea','data/pair_inline-dag.json':'a8fbf064395d2fac5aa041a4c54826938ea2645fba793e0de7500e19f7ca4567','data/anchor_patch.json':'cc67f7c924bcb27ca1c4a48c8d3a630d837b639fbff3032d04515ec1d534ed68','data/endpoint_folded_fixed_numerals_source.json':'dd5a29f925e896bff6759508b4d61c6bee65a18f9e0754d73610f1a0b783d01d'}
 for rel,d in expected.items():need(sha(ROOT/rel)==d,'historical exact source identity '+rel)
 spec=importlib.util.spec_from_file_location('new_recovered_join',ROOT/'merged_source.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 result={'status':'PASS_FRESH_INDEPENDENT_RECOVERED_JOIN','recovery':'New audit implementation and receipts; old byte identity claimed only where freshly hash-verified','generator_sha256':sha(ROOT/'merged_source.py'),'pinned_history_files_verified':len(verified),'optional_external_paths_unavailable':optional_missing,'historical_data_hashes_freshly_verified':expected,'sources':[run(2,m),run(1,m)],'strict_prefix':strict(),'bounded_arithmetic':bounded()}
 (HERE/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
