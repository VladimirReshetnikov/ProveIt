"""Owned provisional incremental decoder allocator. No received program imports.

Old decoder roles are derived by literal prefix walks. Reusing extinct source
states is deliberately only provisional: arithmetic-helper obligations remain.
"""
import direct_screen as D
import mixed_detours as M
from collections import defaultdict,Counter
from functools import lru_cache
import json,sys
def leaf(n):return isinstance(n[0],str)
def tree(sites):
 lm={p:(op,arg)for p,op,arg in sites}
 def rec(p):return lm[p]if p in lm else(rec(p+'0'),rec(p+'1'))
 return rec('')
def nodes(t):
 seen=set()
 def walk(n):
  if leaf(n)or n in seen:return
  seen.add(n);walk(n[0]);walk(n[1])
 walk(t);return seen
def allocation(T,t):
 out=defaultdict(set);pathmap={};gates=[]
 def walk(n,p):
  if leaf(n):return
  tape={-1:1,**{i:int(b)for i,b in enumerate(p)}};initial=tape.copy();q=84;h=0;seen=set()
  while h!=len(p):
   assert q!=254 and h in tape,('unknown prefix',p,q,h)
   key=(q,h,tuple(tape.items()));assert key not in seen;seen.add(key);w,m,q=T[q,tape[h]];tape[h]=w;h+=m
  assert tape==initial,('dirty prefix',p)
  out[q].add(n);pathmap[p]=q
  for b,ch in enumerate(n):
   if leaf(ch):gates.append((ch,b,T[q,b],p+str(b)))
   else:walk(ch,p+str(b))
 walk(t,'');return out,pathmap,gates
def compile(T,old,new):
 groups,paths,gates=allocation(T,old);current=nodes(new);nodeq={n:q for q,ns in groups.items()for n in ns};origins={}
 def match(n,o):
  if leaf(n)or leaf(o):return
  if n!=o:origins.setdefault(n,o)
  match(n[0],o[0]);match(n[1],o[1])
 match(new,old);origins={n:o for n,o in origins.items()if o not in current}
 alternatives=defaultdict(set)
 for op,b,act,p in gates:alternatives[op,b].add(act)
 actions={}
 for key,alts in alternatives.items():
  direct={a for a in alts if a[:2]==(key[1],1)}
  if len(direct)==1:actions[key]=next(iter(direct))
 # Provisional ordinary increment entry: preserve either decoded bit and enter
 # the same existing engine on the following zero-padded address cell. The
 # opposite bit is a new interface obligation, not assumed by source binding.
 for op in {ch for ch,b in alternatives if ch[0]=='CI'}:
  targets={act[2]for (ch,b),acts in alternatives.items()if ch==op for act in acts if act[:2]==(b,1)}
  if len(targets)==1:
   z=next(iter(targets))
   for b in(0,1):actions[op,b]=(b,1,z)
 actions[('CC',1),1]=(0,-1,1)
 actions[('CC',2),1]=(0,-1,16)
 # Existing CI6-left detour 0R13, 0L91, 0R82 reaches true engine82
 # with the complete local patch restored. The generic right entry uses82,
 # not13, whose back-read deliberately distinguishes the decoded source bit.
 actions[('CI',6),1]=(1,1,82)
 # The new generalized break continuation, valid beyond the old short suffix.
 actions[('CB',1),1]=(0,-1,302)
 mapped=dict(nodeq);mapped[new]=84;claimed={84:new};out=T.copy();fresh=max(303,max(q for q,b in T)+1);reused=[];added=[]
 def go(n):
  nonlocal fresh
  if n in mapped:return mapped[n]
  o=origins.get(n);q=nodeq.get(o)
  if q is not None and groups[q]=={o}and q not in claimed:
   reused.append(q)
  else:q=fresh;fresh+=1;added.append(q)
  mapped[n]=q;claimed[q]=n
  for b,ch in enumerate(n):
   if not leaf(ch):out[q,b]=(b,1,go(ch))
   elif o is not None and o in nodeq and o[b]==ch:out[q,b]=T[nodeq[o],b]
   else:assert(ch,b)in actions,('no leaf interface',ch,b);out[q,b]=actions[ch,b]
  return q
 for b,ch in enumerate(new):out[84,b]=(b,1,go(ch))if not leaf(ch)else actions[ch,b]
 reach={0};todo=[0]
 for q in todo:
  for b in(0,1):
   z=out[q,b][2]
   if z!=254 and z not in reach:reach.add(z);todo.append(z)
 out={r:a for r,a in out.items()if r[0]in reach};gg,pp,gate2=allocation(out,new)
 failures=[]
 for q,ns in gg.items():
  for n in ns:
   if mapped.get(n)!=q and n not in groups.get(q,set()):failures.append([q,mapped.get(n)])
 changes=[dict(state=q,read=b,old=T.get((q,b)),new=a)for(q,b),a in out.items()if a!=T.get((q,b))]
 return out,dict(states=len(out)//2,added=added,reused_extinct_decoder_states=reused,removed=sorted({q for q,b in T}-reach),binding_failures=failures,changes=changes,decoder_states=len(gg),roles=sum(map(len,gg.values())),scope='Raw decoder allocation only. Reused old states may retain arithmetic roles; complete primitive proof mandatory.')
def main():
 T=D.table(D.BASE/'k219.native.tm');old=tree(json.loads((D.BASE/'sites219.json').read_text()));summary=[]
 for name in(sys.argv[1:]or['eq_original_02','eq_original_11','shared_cancellation']):
  source=D.D.parent/'research218_source'/f'{name}_sites.json';new=tree(json.loads(source.read_text()));out=D.D/name;out.mkdir(exist_ok=True)
  try:table,receipt=compile(T,old,new);(out/'candidate.native.tm').write_bytes(M.enc(table));receipt.update(source_sha256=D.H(source.read_bytes()),table_sha256=D.H(M.enc(table)))
  except Exception as e:receipt=dict(error=repr(e),status='PRICING_FAILED')
  (out/'RESULT.json').write_text(json.dumps(receipt,indent=2)+'\n');summary.append(dict(name=name,**receipt));print(json.dumps(summary[-1]),flush=True)
 D.dump('DIVERSE_SOURCE_PRICING.json'if sys.argv[1:]else'SOURCE_PRICING.json',summary)
if __name__=='__main__':main()
