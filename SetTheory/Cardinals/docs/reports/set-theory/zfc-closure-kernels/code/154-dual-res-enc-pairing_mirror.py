#!/usr/bin/env python3
"""Source/compiler experiment: globally reverse the Cantor pairing orientation."""
import inverse_mp as q
import json
s,b,z=q.s,q.b,q.z
OUT=q.W/'pairing_mirror';OUT.mkdir(exist_ok=True)
pair=q.get(4689,4699)
loop2=q.get(4678,4686)
loop8=None
for p,op,r in q.ROWS:
 if op=='CD'and r==8:
  pp=p[:-1]
  n=s.subtree(q.TREE,pp)
  if not s.leaf(n)and n[0]==('CD',8)and n[1]==loop2[1]:loop8=n;break
assert loop8

def remap(n,mp):
 if s.leaf(n):return(n[0],mp.get(n[1],n[1]))if n[0]in('CI','CD')else n
 return remap(n[0],mp),remap(n[1],mp)


def transform(n,changes,counters):
 if n in changes:
  counters[str(len(q.x.flat(n)))]+=1
  return changes[n]
 if s.leaf(n):return n
 return transform(n[0],changes,counters),transform(n[1],changes,counters)


def run():
 out=[]
 for kind in ['both','unpair_only','pair_only']:
  ch={}
  if kind!='pair_only':ch.update({loop2:remap(loop2,{6:7,7:6}),loop8:remap(loop8,{6:7,7:6})})
  if kind!='unpair_only':ch[pair]=remap(pair,{6:1,1:6})
  counters={'8':0,'10':0}
  tt=transform(q.TREE,ch,counters);rr=s.sites(tt)
  assert [x[1]for x in s.graph_arithmetic(rr)[0]]==[x[1]for x in s.graph_arithmetic(q.ROWS)[0]]
  assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
  rec={'kind':kind,'source_metrics':s.metrics(tt),'replaced_occurrences':counters,'status':'only both has straightforward new pairing calibration; compiler count requires runtime proof'}
  d=OUT/kind;d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(s.compact(rr))
  try:
   U,m=z.compile_tree(q.T,q.TREE,tt);rec['compiler']=m;(d/'candidate.tm').write_bytes(b.table_bytes(U))
  except Exception as exc:rec['error']=repr(exc)
  (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');out.append(rec);print(json.dumps(rec),flush=True)
 (OUT/'summary.json').write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':run()
