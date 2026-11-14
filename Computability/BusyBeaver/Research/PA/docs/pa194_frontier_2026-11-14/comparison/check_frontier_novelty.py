#!/usr/bin/env python3
"""Exact comparison to all 94 recognized 194-state graphs at the pinned snapshot.

Allows arbitrary control renaming and spanning start, global L/R reflection,
global binary symbol exchange, and ignores the final write/move into halt.
Symbol exchange is deliberately a structural comparison, not a blank-zero
semantic preservation claim. Comparisons use full tuples, not just hashes.
"""
import argparse,hashlib,json,pathlib

def parse(path):
 rows={}
 for line in path.read_text().splitlines():
  if not line.strip() or line.lstrip().startswith(('#','//',';')):continue
  q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
  assert b in (0,1) and w in (0,1) and d in ('L','R') and (q,b) not in rows
  rows[q,b]=(w,d,t)
 states={q for q,b in rows};assert len(rows)==2*len(states)
 halts={t for w,d,t in rows.values()}-states;assert len(halts)==1
 return rows,states,halts.pop()

def rooted(data,start,reflect,complement):
 rows,states,halt=data;labels={start:0};todo=[start];out=[]
 for q in todo:
  for b in (0,1):
   w,d,t=rows[q,b^complement]
   if t==halt:out.append((0,'R',-1));continue
   if t not in labels:labels[t]=len(todo);todo.append(t)
   out.append((w^complement,('R' if d=='L' else 'L') if reflect else d,labels[t]))
 return tuple(out) if len(todo)==len(states) else None

def canonical(data):
 forms=(rooted(data,q,r,c) for r in (False,True) for c in (False,True) for q in sorted(data[1]))
 return min((x for x in forms if x is not None),default=None)

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('candidates',nargs='*',type=pathlib.Path)
 ap.add_argument('--census',type=pathlib.Path,default=pathlib.Path(__file__).parent/'current_census')
 ap.add_argument('--output',type=pathlib.Path)
 args=ap.parse_args()
 index=json.loads((args.census/'frontier194_full.json').read_text())
 references=[];keys={}
 for r in index:
  p=args.census/'representatives'/f"{r['graph_hash']}.tm"
  d=parse(p);assert len(d[1])==194
  can=canonical(d);assert can is not None
  references.append((can,r));keys.setdefault(can,[]).append(r['table_class'])
 output=dict(snapshot='32d0d8b7d93a63ad4106c18cdb29b37927acdad2',reference_graphs=len(references),strong_structural_classes=len(keys),merged_reference_classes=[v for v in keys.values() if len(v)>1],candidate_results=[])
 assert len(references)==94
 for p in args.candidates:
  d=parse(p);can=canonical(d)
  matches=[r['table_class'] for ref,r in references if can==ref]
  output['candidate_results'].append(dict(path=str(p),states=len(d[1]),rows=len(d[0]),raw_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),spanning=can is not None,strong_canonical_sha256=hashlib.sha256(repr(can).encode()).hexdigest(),matching_reference_classes=matches,structurally_new_in_recognized_scope=not matches and can is not None))
 if args.output:args.output.write_text(json.dumps(output,indent=2)+'\n')
 print(json.dumps(output,indent=2))
if __name__=='__main__':main()
