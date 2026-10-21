"""Owned exact baseline prefix-helper census and conservative row-plan filter."""
import search_plateaus as S
from collections import defaultdict,Counter
import json
uses=defaultdict(list)
for p,q in S.paths.items():
 n=S.A.at(S.tree,p)
 for b,ch in enumerate(n):
  if S.P.leaf(ch):continue
  tape={-1:1,**{i:int(c)for i,c in enumerate(p+str(b))}};initial=tape.copy();h=len(p);z=q;step=0
  while h!=len(p)+1:
   assert h in tape and z!=254 and step<100
   read=tape[h];w,d,nz=S.T[z,read]
   if step:uses[z,read].append(dict(prefix=p+str(b),parent_entry=q,step=step))
   tape[h]=w;h+=d;z=nz;step+=1
  assert tape==initial
S.dump('INTERIOR_HELPER_ROWS.json',dict(rows={f'{q}/{b}':dict(count=len(v),examples=v[:5])for(q,b),v in uses.items()},scope='Exact baseline whole-prefix decoding: every non-first transition of an internal-child one-bit decode is an interior helper use. No primitive engine traces included.'))
r=json.load(open(S.OUT/'MARKER_FILTERED_RANKING.json'));okay=[];fail=Counter()
for x in r['ranked']:
 if any(tuple(d['row'])in uses for d in x['changed_rows']):fail['baseline_interior_helper_row']+=1;continue
 if any(d['old'][:2]!=[d['row'][1],1]for d in x['changed_rows']):fail['nonpure_old_row']+=1;continue
 okay.append(x)
S.dump('PURE_ROW_SHORTLIST.json',dict(marker_compatible_plans=r['plans'],excluded=dict(fail),qualified=len(okay),ranked=okay,scope='Conservative source-only local row plans; all modified original rows are bit-preserving R steps and never internal decoder helpers in baseline. No primitive runtime/startup proof. No physical count.'))
print(dict(interior_helper_rows=len(uses),qualified=len(okay),excluded=dict(fail)))
