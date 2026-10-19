"""Generate physical reuse hints from full instruction intervals and source subtrees."""
from pathlib import Path
import sys,json,collections,functools,hashlib
sys.path.insert(0,str(Path(__file__).parent));import compile_rotated as c
base_span={};at=0

def oldwalk(n):
 global at
 start=at
 for e in c.ns[n]:
  if e[0]=='CN':oldwalk(e[1])
  else:at+=1
 base_span[start,at]=n
oldwalk(0)

def hints(graphpath,outpath):
 data=json.load(open(graphpath));E={int(k):v for k,v in data['entries'].items()};O=collections.defaultdict(list)
 @functools.cache
 def canonical(s):
  e=E[s];return c.mk(('N',canonical(e[1]),canonical(e[2]))) if e[0]=='N' else c.mk(tuple(e))
 count=0
 def walk(s,p):
  nonlocal count
  e=E[s]
  if e[0]!='N':count+=1;return
  lo=count;walk(e[1],p+'0');walk(e[2],p+'1');hi=count;old=base_span.get((lo,hi))
  O[s].append(dict(path=p,span=[lo,hi],old_node=old,old_state=None if old is None else c.nq[old]))
 walk(data['root'],'');assert count==6460
 out=[]
 for s,oc in sorted(O.items()):
  structural=sorted(c.sigq.get(canonical(s),set()));same=collections.Counter(o['old_state'] for o in oc if o['old_state'] is not None)
  out.append(dict(grammar_node=s,children=E[s][1:],occurrence_count=len(oc),original_structural_states=structural,same_interval_old_states=sorted(same.items()),occurrences=oc))
 result=dict(graph_sha256=hashlib.sha256(Path(graphpath).read_bytes()).hexdigest(),root=data['root'],entries=out)
 Path(outpath).write_text(json.dumps(result,separators=(',',':'))+'\n');return result
if __name__=='__main__':hints(sys.argv[1],sys.argv[2])
