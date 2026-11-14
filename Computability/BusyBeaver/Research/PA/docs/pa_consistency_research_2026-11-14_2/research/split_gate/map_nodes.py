from probe_macros import *
import collections
mpath=base/'docs/pa196_research_2026-11-13/search/rotations/allocator-screen'
sys.path.insert(0,str(mpath));import source_language as s
from build221 import decoder_map
p=base/'docs/pa194_conpa_2026-11-13/construction'
lab=json.loads((p/'tables/pa194.labels.json').read_text());T={}
for l in (p/'tables/pa194.tm').read_text().splitlines():
 q,b,w,d,n=l.split();T[lab[int(q)],int(b)]=(int(w),1 if d=='R' else -1,lab[int(n)])
ops={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
rows=[[p,ops[o],a]for p,o,a in json.loads((p/'source/pa194.sites.json').read_text())]
tree=s.tree(rows);G,paths=decoder_map(T,tree)
rev=collections.defaultdict(list)
for q,ts in G.items():
 for t in ts:rev[t].append(q)
def en(t):
 if isinstance(t,str):return en(nodes[t])
 if t[0]=='leaf':return ops[t[1]],t[2]
 return tuple(map(en,t))
if __name__=='__main__':
 for name in ['node17','node6','node19','node145','node146','node150']:
  print(name,rev.get(en(name)))
 actions=collections.defaultdict(set)
 for q,ts in G.items():
  for t in ts:
   for b,k in enumerate(t):
    if s.leaf(k):actions[k,b].add(T[q,b])
 for a,v in sorted(actions.items(),key=str):print(a,v)
