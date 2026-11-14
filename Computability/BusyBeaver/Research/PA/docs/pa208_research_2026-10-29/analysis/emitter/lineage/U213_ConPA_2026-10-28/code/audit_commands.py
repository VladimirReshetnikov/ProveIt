#!/usr/bin/env python3
"""Bind U213's scheduler, command decoder, AX preamble, MP, and S to ProgLib.

Finite exact source/DAG audit, not a proof-assistant kernel. Each referenced
all-natural macro contract is retained as a named ProgLibPerm.v lemma.
"""
from pathlib import Path
import argparse,hashlib,json,re

SOURCE_SHA='7b6539dc67b66ff73f22554018d7af5985d85574460a73fea5f025103c523d00'
DAG_SHA='ba2b28487ae978bd27b0d804e9b2bde6d9adcd1dd575de55572465c050b86aa1'
CALLS=[(0,9,133,'ifnot133'),(9,23,174,'read174'),
       (25,51,166,'par166'),(51,77,121,'par121'),(77,106,180,'wal180'),
       (3767,3781,175,'read175'),(3781,3807,166,'par166'),
       (3807,3834,119,'cons119'),(3834,3837,216,'w216'),(3837,3873,130,'ifeq130'),
       (3874,3876,214,'w214'),(3876,3880,200,'w200'),(3880,3883,207,'w207'),
       (3884,3895,132,'ifeq132_halt / ifeq132_normal'),(3895,3909,170,'pop170')]
def need(p,why):
 if not p:raise ValueError(why)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def cfg(rows):
 bounds={}
 for i,(p,o,a)in enumerate(rows):
  for j in range(len(p)+1):
   k=p[:j]
   if k not in bounds:bounds[k]=[i,i+1]
   else:bounds[k][1]=i+1
 graph=[]
 for i,(p,o,a)in enumerate(rows):
  if o=='CI':dst=(i+1,)
  elif o=='CH':dst=()
  else:
   bit='1'if o=='CC'else'0';n=a if o!='CD'else 1;positions=[j for j,b in enumerate(p)if b==bit]
   need(len(positions)>=n,'Escaping control edge');v=bounds[p[:positions[-n]]][0 if o=='CC'else 1]
   dst=(v,i+1)if o=='CD'else(v,)
  graph.append((o,a,dst))
 return graph
def dag_nodes(raw):
 edge=r'(?:ENode|EInc|EDecnz|EBreak|EContinue)\s+\d+|EHalt'
 ns={int(n):(a,b)for n,a,b in re.findall(r'^\s*\|\s*(\d+)\s*=>\s*\(('+edge+r'),\s*('+edge+r')\)\s*$',raw.decode('ascii'),re.M)}
 need(len(ns)==487,'Wrong arithmetic DAG size')
 def unfold(edge,p='',anc=frozenset()):
  xs=edge.split();kind=xs[0]
  if kind=='ENode':
   n=int(xs[1]);need(n in ns and n not in anc,'Invalid DAG');a,b=ns[n];return unfold(a,p+'0',anc|{n})+unfold(b,p+'1',anc|{n})
  return[[p,{'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC','EHalt':'CH'}[kind],None if kind=='EHalt'else int(xs[1])]]
 return{n:cfg(unfold('ENode '+str(n)))for lo,hi,n,lemma in CALLS}
def bind(graph,proof,lo,hi):
 actual=[(o,r,tuple(x-lo for x in dst))for o,r,dst in graph[lo:hi]]
 need(len(actual)==len(proof),'Macro arity differs');need([d for o,r,d in actual]==[d for o,r,d in proof],'Macro control edges differ')
 need(all(0<=x<=hi-lo for o,r,d in actual for x in d),'Macro has escaping nonnormal edge')
 edits=[];i=0
 while i<len(proof):
  o,r,d=actual[i];q,k,e=proof[i]
  if(o,r,d)==(q,k,e):i+=1;continue
  if o==q and o in('CB','CC'):
   edits.append({'kind':'same resolved jump','relative_ordinal':i,'source_depth':r,'proof_depth':k});i+=1;continue
  need(o==q=='CI'and i+1<len(proof),'Unjustified primitive difference')
  o2,r2,d2=actual[i+1];q2,k2,e2=proof[i+1]
  need(o2==q2=='CI'and(r,r2)==(k2,k),'Not independent increment commutation')
  need(d==(i+1,)and d2==(i+2,),'Increment pair does not fall through')
  need(all(lo+i+1 not in dest for j,(op,a,dest)in enumerate(graph)if j!=lo+i),'Entry into swapped increment interior')
  edits.append({'kind':'commuting consecutive increments','relative_ordinals':[i,i+1],'source_registers':[r,r2],'proof_registers':[k,k2]});i+=2
 return edits
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--source',type=Path,required=True);p.add_argument('--dag',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 raw=a.source.read_bytes();dr=a.dag.read_bytes();need(sha(raw)==SOURCE_SHA,'Wrong source');need(sha(dr)==DAG_SHA,'Wrong arithmetic DAG')
 rows=json.loads(raw);g=cfg(rows);ns=dag_nodes(dr);bindings=[]
 for lo,hi,n,lemma in CALLS:bindings.append({'start':lo,'stop':hi,'dag_node':n,'lemma':'ProgLibPerm.'+lemma,'normalizations':bind(g,ns[n],lo,hi)})
 expected={23:('CD',3,(3874,24)),24:('CD',3,(3767,25)),3766:('CB',1,(3873,)),3873:('CC',3,(0,)),3883:('CI',6,(3884,))}
 for i,want in expected.items():need(g[i]==want,('Command branch differs',i,g[i],want))
 need(rows[3894][1:]==['CH',None],'S halt missing');need(sum(o=='CH'for p,o,r in rows)==1,'Unexpected source halt')
 covered=set()
 for lo,hi,n,l in CALLS:covered.update(range(lo,hi))
 covered.update(expected)
 need(covered==set(range(106))|set(range(3766,3909)),'Command exterior partition incomplete')
 result={'status':'EXACT_SCHEDULER_DECODER_AX_PREAMBLE_MP_S_BINDING_PASS','source_sha256':sha(raw),'dag_sha256':sha(dr),'macro_bindings':bindings,'single_primitive_controls':[{ 'ordinal':i,'effect':g[i]}for i in expected],'covered_primitive_occurrences':len(covered),'scope':'Complete exact command exterior binding. The named all-natural arithmetic lemmas and the written composition prove command effects; binary runtime and initializer remain separate.'}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in('macro_bindings',)},indent=2))
if __name__=='__main__':main()
