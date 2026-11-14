from pathlib import Path
import json,itertools,ast,collections,time
ROOT=Path(__file__).parent
d=json.loads((ROOT/'jump_options.json').read_text())
base={(q,b):(w,bool(m),n) for q,b,w,m,n in d['rows']}
options={ast.literal_eval(k):[tuple(x) for x in opts] for k,opts in d['options'].items() if len(opts)>1}
def quotient(rows):
 controls={q for q,b in rows};part={q:0 for q in controls};part[254]=1
 while True:
  index={};new={254:-1}
  for q in sorted(controls):
   sig=tuple((rows[q,b][:2]+(part[rows[q,b][2]],)) for b in(0,1))
   new[q]=index.setdefault(sig,len(index))
  if all(part[a]==part[b] for a,b in []) and len(set(new.values()))==len(set(part.values())):break
  part=new
 groups=collections.defaultdict(list)
 for q,v in new.items():groups[v].append(q)
 return [qs for qs in groups.values() if len(qs)>1]
def opportunities(rows):
 controls={q for q,b in rows};incoming=collections.defaultdict(set)
 for (q,b),(w,m,n) in rows.items():incoming[n].add((w,m))
 left=[q for q in controls if incoming[q]=={(0,True)} and q!=74]
 right=[q for q in controls if incoming[q]=={(1,True)} and q!=74]
 providers=[collections.defaultdict(list),collections.defaultdict(list)]
 for h in controls:
  w0,d0,u0=rows[h,0];w1,d1,u1=rows[h,1]
  if w0 or w1!=1 or not d0 or not d1:continue
  for bit in(0,1):
   if (u0,bit) in rows and(u1,bit)in rows:providers[bit][rows[u0,bit],rows[u1,bit]].append((h,u0,u1))
 out=[]
 for a in left:
  for b in right:
   if a==b:continue
   choices=[]
   for bit in (0,1):
    if rows[a,bit]==rows[b,bit]:choices.append([rows[a,bit]])
    else:choices.append([(bit,False,h) for h,u0,u1 in providers[bit].get((rows[a,bit],rows[b,bit]),[]) if not {a,b}&{h,u0,u1}])
   if all(choices):out.append((a,b,choices))
 return out
found=[];count=0
for acts in itertools.product(*options.values()):
 rows=dict(base);edits=dict(zip(options,acts));rows.update(edits);count+=1
 eq=quotient(rows);ops=opportunities(rows)
 if eq or ops:
  item={'edits':[[q,b,*a] for(q,b),a in edits.items()],'quotient_groups':eq,'folds':ops}
  found.append(item);print(json.dumps(item),flush=True)
(ROOT/'joint_candidates.json').write_text(json.dumps({'combinations':count,'candidates':found},indent=2))
print('combinations',count,'candidates',len(found),flush=True)
