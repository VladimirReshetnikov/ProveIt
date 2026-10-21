import complement_quantifier as c
from difflib import SequenceMatcher
import json
c.spans['GEN']=(40,121)
results=[]
for mode in ['coforall','exists']:
 fs=c.gen_transformed(mode);hunks=[]
 for name,(lo,hi) in c.spans.items():
  old=c.postfix(c.forms[name]);new=c.postfix(fs[name]);offsets=[lo]
  for x in old:offsets.append(offsets[-1]+len(c.m.flat(c.mac[x])))
  assert offsets[-1]==hi
  ops=SequenceMatcher(None,old,new,autojunk=False).get_opcodes();patches=[]
  for tag,i,j,k,l in ops:
   if tag=='equal':continue
   if i==j:
    if i>0:i-=1;k-=1
    else:j+=1;l+=1
   if patches and patches[-1][1]>=i:
    z=patches.pop();patches.append((z[0],j,z[2],l))
   else:patches.append((i,j,k,l))
  for i,j,k,l in patches:
   nodes=[c.mac[x]for x in new[k:l]];rep=c.m.serial(nodes)if nodes else None
   hunks.append((offsets[i],offsets[j],rep,name,old[i:j],new[k:l]))
 rr=c.tree
 for lo,hi,rep,name,old,new in sorted(hunks,reverse=True):
  try:rr=c.m.splice(c.s,rr,lo,hi,rep)
  except ValueError as e:print('SPLICE_FAIL',mode,name,lo,hi,old,new,e,flush=True);raise
 metrics=c.s.metrics(rr);print('LOCAL',mode,metrics,flush=True)
 c.s.graph_arithmetic(c.s.sites(rr));assert c.s.graph_arithmetic(c.s.sites(rr))[0]==c.s.graph_intervals(c.s.sites(rr))
 (c.H/(mode+'.local.sites.json')).write_bytes(c.s.compact(c.s.sites(rr)))
 results.append({'mode':mode,'metrics':metrics,'hunks':[{'lo':lo,'hi':hi,'formula':name,'old':old,'new':new}for lo,hi,rep,name,old,new in hunks]})
(c.H/'complement_quantifier_local_results.json').write_text(json.dumps(results,indent=2)+'\n')
