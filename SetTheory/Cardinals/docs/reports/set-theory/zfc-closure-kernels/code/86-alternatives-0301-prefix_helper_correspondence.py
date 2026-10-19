#!/usr/bin/env python3
"""Independent guarded counter-program comparison for 20 mapped helpers.
Control-only jumps are erased. Adjacent increments are aggregated by register;
they commute on every natural register valuation. Every decrement guard/exit
is compared by a finite graph bisimulation. No sampled register values.
"""
from pathlib import Path
from collections import Counter,deque
import sys,json,hashlib
if not __debug__:raise RuntimeError('Run without -O.')
HERE=Path(__file__).resolve().parent;R=HERE.parent;B=R/'context_folds/recovered/67/research'
sys.path[:0]=[str(B/'agent_logic'),str(R/'source/Computability/BusyBeaver/Research/ZFC')]
from verify_reassociation import Decoder,read_json
import recover_wade_dag as rec
old,_=rec.parse_dag(rec.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
def edge(e):
 s=e.split();return ('H',) if s[0]=='EHalt' else ({'ENode':'N','EInc':'I','EDecnz':'D','EBreak':'B','EContinue':'C'}[s[0]],int(s[1]))
old={q:tuple(map(edge,e)) for q,e in old.items()}
new,root,h=read_json(B/'sources/beyond252/beyond252/exploratory/data/original203.json')
eq=max(new)+1;new[eq]=(('N',58),('I',1))
mp={166:43,121:48,168:63,171:39,177:91,119:57,181:79,180:58,182:eq,218:92,178:132,183:94,176:60,158:18,208:30,192:160,131:171,211:11,197:172,161:68}
def graph(nodes,q):
 n=nodes.copy();wrapper=max(n)+1;n[wrapper]=(('N',q),('H',));d=Decoder(n,wrapper)
 assert d.bounds(('N',q))==(0,0)
 return d.graph(),d

def skip(g,i):
 counts=Counter();seen=set()
 while True:
  op,succ=g[i]
  if op[0] in ('D','H'):return tuple(sorted(counts.items())),i
  if i in seen:raise RuntimeError('Non-decrement control/increment cycle')
  seen.add(i)
  if op[0]=='I':counts[op[1]]+=1
  else:assert op[0] in ('B','C')
  assert len(succ)==1;i=succ[0]

def compare(ga,gb):
 todo=deque([(0,0)]);seen=set();witness=[]
 while todo:
  a,b=todo.popleft()
  ca,aa=skip(ga,a);cb,bb=skip(gb,b)
  assert ca==cb,('increment vectors',a,b,ca,cb)
  oa,sa=ga[aa];ob,sb=gb[bb]
  assert oa==ob,('guard/op',a,b,oa,ob)
  if (aa,bb) in seen:continue
  seen.add((aa,bb));witness.append(dict(old_site=aa,new_site=bb,increments=ca,op=oa,old_successors=sa,new_successors=sb))
  assert len(sa)==len(sb)
  todo.extend(zip(sa,sb))
 return witness
results={}
for a,b in mp.items():
 ga,da=graph(old,a);gb,db=graph(new,b);w=compare(ga,gb)
 results[a]=dict(mapped_helper=b,closed_escape_bounds=True,old_leaf_sites=len(ga),new_leaf_sites=len(gb),guarded_bisimulation_pairs=len(w),witness=w)
report=dict(status='PASS',comparison='All-register guarded CFG bisimulation modulo finite commuting increment blocks',old_source='pinned Dag254.v',new_source_sha256=h,helpers=results,helper_count=len(results),obligation='A formal bridge from this finite certificate to Lean RegisterPath semantics remains; ordinary bisimulation argument is given in helper_correspondence.md.')
(HERE/'prefix_helper_correspondence_results.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(status='PASS',helper_count=len(results),guarded_pairs=sum(x['guarded_bisimulation_pairs'] for x in results.values())),indent=2))
