#!/usr/bin/env python3
"""Owned standalone audit of the failed scratch-biased source binding."""
from pathlib import Path
from functools import lru_cache
import argparse,hashlib,json,sys

def leaf(t):return isinstance(t[0],str)
def tree(sites):
 d={p:(op,k)for p,op,k in sites}
 assert len(d)==len(sites)
 def go(p):return d[p]if p in d else(go(p+'0'),go(p+'1'))
 return go('')
@lru_cache(None)
def length(t):return 1 if leaf(t)else length(t[0])+length(t[1])
def at(t,p):
 for b in p:t=t[int(b)]
 return t
def put(t,p,x):
 if not p:return x
 b=int(p[0]);return tuple(put(t[i],p[1:],x)if i==b else t[i]for i in(0,1))
def flatten(t):
 out=[]
 def go(n,p):
  if leaf(n):out.append([p,*n])
  else:go(n[0],p+'0');go(n[1],p+'1')
 go(t,'');return out
def graph(t):
 out=[];N=length(t)
 def go(n,i,bs,cs):
  if leaf(n):
   op,k=n;after=(i+1)%N
   dest=lambda stack,j:stack[-j]%N if len(stack)>=j else 0
   edges=[]if op=='CH'else[dest(cs,k)]if op=='CC'else[dest(bs,k)]if op=='CB'else[dest(bs,1),after]if op=='CD'else[after]
   assert len(out)==i;out.append([op,None if op in('CB','CC')else k,edges]);return
  go(n[0],i,bs+[i+length(n)],cs);go(n[1],i+length(n[0]),bs,cs+[i])
 go(t,0,[],[]);return out
def find(t,wanted):
 out=[]
 def go(n,p,i):
  if n==wanted:out.append({'path':p,'start':i,'end':i+length(n)})
  if not leaf(n):go(n[0],p+'0',i);go(n[1],p+'1',i+length(n[0]))
 go(t,'',0);return out
def compact(x):return(json.dumps(x,separators=(',',':'))+'\n').encode()
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def audit(source,parent):
 assert H(source)=='2407f815551b4aba335c9bf041e15e8ce3cfb9ad830d89539f3bcf123462371a'
 assert H(parent)=='05e7caa159d95cdf9ee254d313c44c52369ac91e52cbc23d54b15f0b64b95922'
 sites=json.loads(source.read_text());oldsites=json.loads(parent.read_text());n=tree(sites);old=tree(oldsites)
 assert flatten(n)==sites and flatten(old)==oldsites
 transfer=at(old,'111');drop,nip=transfer[0];assert transfer[1]==nip
 clear=(('CD',1),('CC',1));load=drop[1]
 assert length(drop)==26 and length(nip)==26 and length(load)==7
 simple=put(old,'111',((clear,load),nip));g=graph(n);expected=graph(simple)
 extra=4696;assert sites[extra]==['100110','CI',6] and g[extra][2]==[4697]
 norm=lambda op:'JUMP'if op in('CB','CC')else op
 contracted=[]
 for i,(op,k,edges)in enumerate(g):
  if i==extra:continue
  es=[z-1 if z>extra else z for z in [extra+1 if z==extra else z for z in edges]]
  contracted.append([norm(op),k,es])
 ref=[[norm(op),k,edges]for op,k,edges in expected]
 diffs=[[i,a,b]for i,(a,b)in enumerate(zip(contracted,ref))if a!=b]
 assert len(contracted)==len(ref)==4732
 assert diffs==[[4696,['JUMP',None,[23]],['JUMP',None,[0]]]]
 blocks={}
 for label,body in [('AX',at(old,'1101001')),('MP',at(old,'110101')),('load',load),('NIP',nip)]:
  places=find(n,body);assert places;blocks[label]={'leaves':length(body),'occurrences':places}
 assert blocks['AX']['occurrences']==[{'path':'1001001','start':25,'end':4590}]
 assert blocks['MP']['occurrences']==[{'path':'100101','start':4590,'end':4696}]
 assert at(n,'00')==old[0] and at(n,'01')==at(old,'10')
 assert g[4697]==['CC',None,[23]] and g[23]==['CD',3,[4698,24]]
 assert g[4698]==['CD',1,[4700,4699]] and g[4699]==['CC',None,[4698]]
 base=[]
 for top in range(51):
  regs=[37,top,91,0,59,0,0,0,0];pc=4696;trace=[]
  for tick in range(300):
   op,k,edges=g[pc];trace.append([pc,op,k,regs[:]])
   if op=='CH':break
   if op=='CI':regs[k]+=1;pc=edges[0]
   elif op=='CD':b=int(regs[k]>0);regs[k]-=b;pc=edges[b]
   else:pc=edges[0]
  else:raise AssertionError('Probe cap')
  assert pc==4718 and tick==15+2*top and regs==[37,0,91,0,59,0,0,0,0]
  if top==0:base=trace
 assert {row[2]for row in base if row[1]in('CD','CI')}=={1,3,5,6}
 return {'status':'SOURCE_BINDING_DEFECT_AND_POST_AX_HALT_PROVED','source_sha256':H(source),'parent_sha256':H(parent),'leaf_count':len(sites),'single_contracted_CFG_difference':diffs,'unchanged_blocks':blocks,'schedule_and_read_unchanged':True,'post_AX_halt':{'entry':4696,'halt_ordinal':4718,'source_steps_to_CH':'15+2*T','conditions':{'A':0,'H':0,'X':0,'Y':0},'arbitrary_untouched':['N','W','D','L'],'clear_loop':[4698,4699],'base_trace':base,'finite_duration_probes':51},'scope':'Exact finite source/CFG facts and fixed trace plus a natural-number clear-loop induction. Blank-to-AX binding and binary simulation are separate obligations. No received code executed.'}
def main():
 if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must be enabled')
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--parent',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 out=audit(a.source,a.parent);a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(out,indent=2)+'\n');print(out['status'])
if __name__=='__main__':main()
