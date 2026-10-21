"""Owned static incoming-marker/pair ranking; no selector execution or new search."""
import search_plateaus as S
import json,itertools
from collections import defaultdict,Counter
plans=json.load(open(S.OUT/'PURE_ROW_SHORTLIST.json'))['ranked']
def pairs(T):
 incoming=defaultdict(list)
 for row,act in T.items():incoming[act[2]].append((row,act))
 markers={q:next(iter({act[0]for row,act in rows}))for q,rows in incoming.items()if q!=0 and all(act[1]==1 for row,act in rows)and len({act[0]for row,act in rows})==1}
 out=[];states=sorted({q for q,b in T})
 for q,r in itertools.combinations(states,2):
  if q not in markers or r not in markers or markers[q]==markers[r]:continue
  same=[b for b in(0,1)if T[q,b]==T[r,b]]
  if not same:continue
  out.append(dict(states=[q,r],markers=[markers[q],markers[r]],shared_reads=same,actions=[[list(T[q,b]),list(T[r,b])]for b in(0,1)]))
 return out
base=pairs(S.T);known={tuple(x['states'])for x in base}
for x in plans:
 table=S.T.copy()
 for d in x['changed_rows']:table[tuple(d['row'])]=tuple(d['new'])
 allpairs=pairs(table);new=[p for p in allpairs if tuple(p['states'])not in known]
 x['new_marked_pairs']=new
 x['lost_marked_pairs']=[list(p)for p in sorted(known-{tuple(p['states'])for p in allpairs})]
 x['scope']+=' Static candidate incoming-marker pairs are opportunities only; helper selection, prefix binding and universal contracts unproved.'
plans.sort(key=lambda x:(-bool(x['new_marked_pairs']),x['displaced_physical_role_count'],x['changed_row_count'],-len(x['new_marked_pairs']),len(x['steps']),x['source_sha256']))
S.dump('SELECTOR_OPPORTUNITY_SHORTLIST.json',dict(sources=len(plans),sources_with_new_marked_pairs=sum(bool(x['new_marked_pairs'])for x in plans),baseline_marked_pairs=len(base),ranked=plans))
print('with new pairs',sum(bool(x['new_marked_pairs'])for x in plans))
for x in plans[:12]:print(json.dumps(x))
