"""Six nonzero-tag permutations; source-only candidates, not runtime certification."""
import complement_quantifier as c
import itertools,json,hashlib
c.spans['GEN']=(40,121)
s,m=c.s,c.m
out=[]
for perm in itertools.permutations([1,2,3]):
 tags=dict(zip('RQE',perm));mac=dict(c.mac)
 incseq={1:c.inc,2:(c.inc,c.inc),3:((c.inc,c.inc),c.inc)}
 for k in 'RQE':mac[k]=(c.imp,incseq[tags[k]])
 mac['F']=(c.push,incseq[tags['R']])
 patches=[]
 for name,(lo,hi) in c.spans.items():
  offset=lo
  for tok in c.postfix(c.forms[name]):
   n=len(m.flat(c.mac[tok]));new=mac[tok]
   if new!=c.mac[tok]:patches.append((offset,offset+n,new,name,tok))
   offset+=n
  assert offset==hi
 if tags['R']!=1:patches.append((4598,4599,m.serial([('CI',6)]*tags['R']),'NIP','target'))
 rr=c.tree
 for lo,hi,new,name,tok in sorted(patches,reverse=True):rr=m.splice(s,rr,lo,hi,new)
 rows=s.sites(rr);assert s.graph_arithmetic(rows)[0]==s.graph_intervals(rows)
 name='retag-'+''.join(map(str,perm));raw=s.compact(rows);(c.H/(name+'.sites.json')).write_bytes(raw)
 r={'name':name,'tags':tags,'source_metrics':s.metrics(rr),'source_sha256':hashlib.sha256(raw).hexdigest(),'patch_count':len(patches)}
 print(r,flush=True);out.append(r)
(c.H/'retag_constructors_results.json').write_text(json.dumps(out,indent=2)+'\n')
