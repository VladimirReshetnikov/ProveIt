from pathlib import Path
import json,sys,collections
sys.path.insert(0,str(Path(__file__).parent));import compile_rotated as c
HERE=Path(__file__).parent
G=json.load(open(HERE.parent/'agent_logic/rotation_zero_candidate_24.json'));E={int(s):v for s,v in G['entries'].items()}
roles={int(s):q for s,q in json.load(open(HERE/'compiled24_raw_roles.json'))['roles'].items()}
roles.update({7844:258,181:259,11555:260})
qs=collections.defaultdict(list)
for s,q in roles.items():qs[q].append(s)
T=c.T.copy()
for q,ss in qs.items():
 for b in (0,1):
  wants=[]
  for s in ss:
   child=E[E[s][b+1]]
   if child[0]=='N':row=(b,'R',roles[E[s][b+1]])
   else:
    opts={c.T[q,b] for sg in c.qsig.get(q,set()) if c.entries[c.entries[sg][b+1]]==tuple(child)}
    row=next(iter(opts)) if len(opts)==1 else c.term[tuple(child)+(b,)].most_common(1)[0][0]
   wants.append(row)
  if len(set(wants))==1:T[q,b]=wants[0]
  else:print('KEPT',q,b,wants)
c.save_table(T,HERE/'compiled24_cloned251.tm')
(HERE/'compiled24_cloned251_roles.json').write_text(json.dumps({'roles':roles},indent=2)+'\n')
print('COUNT',len({q for q,b in T}))
