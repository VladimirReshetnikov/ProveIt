#!/usr/bin/env python3
"""Check closed affine fragments for invariant-supported replacements."""
import total_fragment_summaries as t
import json,collections
states=json.loads((t.ROOT/'experiments/audit_inputs/reduced_affine_certificate.json').read_text())['states']
graph=t.D.graph();pred=[set() for _ in graph]
for i,(_,ns) in enumerate(graph):
 for j in ns:pred[j].add(i)
regions=collections.defaultdict(list);cursor=0

def walk(e,p):
 global cursor
 if e[0]!='N':cursor+=1;return
 low=cursor
 for bit,ch in enumerate(t.nodes[e[1]]):walk(ch,p+str(bit))
 high=cursor
 regions[e[1]].append((low,high,p))
walk(('N',t.root),'')
options={('N',n):t.summary(('N',n)) for n in t.nodes if t.summary(('N',n)) is not None}
options.update({('I',r):t.incr(r) for r in range(9)})
options[('empty',)]=t.identity
replacements=[];badentry=[]
for n in t.proof:
 regs=regions[n]
 if any(any(i<lo or i>=hi for i in pred[j]) for lo,hi,p in regs for j in range(lo+1,hi)):
  badentry.append(n);continue
 vectors=[v for lo,hi,p in regs for v in states[lo]]
 M=t.summary(('N',n))
 for e,A in options.items():
  if e==('N',n):continue
  difference=[[a-b for a,b in zip(m,alt)] for m,alt in zip(M,A)]
  if all(sum(a*b for a,b in zip(row,v))==0 for row in difference for v in vectors):
   replacements.append({'node':n,'alternative':e,'regions':len(regs),'admitted_entry_regions':sum(bool(states[lo]) for lo,hi,p in regs),'definition':t.nodes[n]})
res={'closed_affine_nodes':len(t.proof),'options':len(options),'improper_entry_nodes':badentry,'replacements':replacements}
(t.Path.cwd()/'affine_fragment_replacements.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res,indent=2))
