#!/usr/bin/env python3
"""Replay exact structural novelty, without a hash-isomorphism assumption.
Each working control contributes (working indegree, self-loop row count,
whether its two successors agree). The histogram is invariant under state
renaming, start choice, reflection, global symbol exchange, and changes to
terminal-edge write/move. An unequal multiplicity is an exact witness.
Hashes in the manifest are byte-identity checks, not the isomorphism proof.
"""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json
HERE=Path(__file__).resolve().parent

def parse(path):
 rows={}
 for line in path.read_text().splitlines():
  if not line.strip() or line.lstrip().startswith('#'):continue
  q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
  if (q,b) in rows or b not in (0,1) or w not in (0,1) or d not in ('L','R'):raise ValueError('invalid row')
  rows[q,b]=(w,d,t)
 states={q for q,b in rows}
 if len(states)!=194 or len(rows)!=388 or any((q,b) not in rows for q in states for b in (0,1)):raise ValueError('not a complete194-state binary table')
 halts={a[2] for a in rows.values()}-states
 if len(halts)!=1:raise ValueError('expected exactly one external halt')
 return rows,states

def histogram(table):
 rows,states=table;incoming=Counter(t for _,_,t in rows.values() if t in states)
 return Counter((incoming[q],sum(rows[q,b][2]==q for b in (0,1)),int(rows[q,0][2]==rows[q,1][2])) for q in states)

def coded(hist):return [[*k,v] for k,v in sorted(hist.items())]

def witness(a,b):
 for k in sorted(set(a)|set(b)):
  if a[k]!=b[k]:return {'triple':list(k),'candidate_multiplicity':a[k],'reference_multiplicity':b[k]}
 return None

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--manifest',type=Path,default=HERE/'novelty_manifest.json')
 ap.add_argument('--output',type=Path)
 a=ap.parse_args();manifest=json.loads(a.manifest.read_text());base=a.manifest.parent
 candidates=[];records=[]
 for rec in manifest['candidates']:
  p=base/rec['file'];data=p.read_bytes()
  if hashlib.sha256(data).hexdigest()!=rec['sha256']:raise ValueError('candidate bytes changed: '+str(p))
  table=parse(p);profile=histogram(table)
  # The preserved blank start is checked independently of start-free novelty.
  rows,states=table;seen={rec['start']};queue=[rec['start']]
  for q in queue:
   for bit in (0,1):
    t=rows[q,bit][2]
    if t in states and t not in seen:seen.add(t);queue.append(t)
  if seen!=states:raise ValueError('candidate not graph-spanning from start')
  candidates.append((rec,profile))
 for rec in manifest['prior_tables']:
  p=base/rec['file'];data=p.read_bytes()
  if hashlib.sha256(data).hexdigest()!=rec['sha256']:raise ValueError('reference bytes changed: '+str(p))
  profile=histogram(parse(p));w=[]
  for cand,hist in candidates:
   found=witness(hist,profile)
   if found is None:raise ValueError('profile does not separate '+cand['name']+' from '+rec['file'])
   w.append({'candidate':cand['name'],**found})
  records.append({'file':rec['file'],'histogram':coded(profile),'witnesses':w})
 pairs=[]
 for i,(r,h) in enumerate(candidates):
  for s,k in candidates[i+1:]:
   found=witness(h,k)
   if found is None:raise ValueError('candidate profiles not separated')
   pairs.append({'candidate':r['name'],'reference':s['name'],**found})
 result={'ok':True,'commit':manifest['commit'],'scope':manifest['scope'],'prior_normalized_tables':len(records),'candidate_histograms':{r['name']:coded(h) for r,h in candidates},'candidate_pair_witnesses':pairs,'prior_witnesses':records,'graph_isomorphism_decision_uses_hashes':False,'warning':'Structural novelty is separate from halting-equivalence correctness.'}
 if a.output:a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ('prior_witnesses','candidate_histograms')},indent=2))
if __name__=='__main__':main()
