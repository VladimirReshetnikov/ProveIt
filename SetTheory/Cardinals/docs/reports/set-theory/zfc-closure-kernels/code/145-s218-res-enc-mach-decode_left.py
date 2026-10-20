import json
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import compile_eq as c
at=json.loads((Path(__file__).resolve().parent/'eqatoms.json').read_text());nodes={i:c.tup(x)for i,x in enumerate(at)};hits=[]
for line in (Path(__file__).resolve().parent/'output/eq_left_nodes.txt').read_text().splitlines():
 a=line.split()
 if a[0]=='H':hits.append((nodes[int(a[1])],nodes[int(a[2])]))
 else:
  i,a,b,k=map(int,a);nodes[i]=(nodes[a],nodes[b])
seen=set();out=[]
for i,h in enumerate(hits):
 if h in seen:continue
 seen.add(h);tr=c.repl(c.TREE,c.OLD,h);m=c.s.metrics(tr)
 r={'hit':i,'metrics':m,'macro_metrics':c.s.metrics(h),'tree':h}
 print('HIT',i,'whole',m['dag_nodes'],'macro',c.s.metrics(h)['dag_nodes'],repr(h))
 out.append(r)
(Path(__file__).resolve().parent/'left_hits.json').write_text(json.dumps(out,indent=2))
