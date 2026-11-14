#!/usr/bin/env python3
"""Independent literal-table comparison of all designated U208 outputs.

This does not prove a consistency calibration. It verifies exact rooted
action-preserving isomorphism by canonical breadth-first numbering.
"""
import collections,hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parent
SELECTED={
 'ConPA primary':'U208_ConPA_2026-10-29/U208_ConPA_2026-10-29/machine/u208.tm',
 'Conditional primary':'U208_ConPA_Conditional_Context_2026-10-29/u208_conpa_2026-10-29/machine/u208.tm',
 'Conditional alternative':'U208_ConPA_Conditional_Context_2026-10-29/u208_conpa_2026-10-29/alternative/u208.tm',
 'Entry primary':'U208_ConPA_Entry_Context_2026-10-29/u208_conpa_entry_context_2026-10-29/machine/u208.tm',
 'Entry alternative':'U208_ConPA_Entry_Context_2026-10-29/u208_conpa_entry_context_2026-10-29/machine/u208_compatibility.tm',
 'History primary':'U208_ConPA_History_2026-10-29/U208_ConPA_History_2026-10-29/machine/u208.tm',
 'History alternative':'U208_ConPA_History_2026-10-29/U208_ConPA_History_2026-10-29/machine/compatibility_variant/u208.tm',
 'Research primary':'u208_research_2026-10-29/u208_research_2026-10-29/machine/u208.tm',
 'Research alternative':'u208_research_2026-10-29/u208_research_2026-10-29/machine/variant_plain/u208.tm',
}
def load_table(path):
 out={}
 for line in path.read_text().splitlines():
  if not line.strip() or line.lstrip().startswith('#'):continue
  q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
  if b not in (0,1) or w not in (0,1) or d not in ('L','R') or (q,b) in out:raise ValueError(line)
  out[q,b]=(w,d,t)
 return out
def canon(tab,start=0):
 states={q for q,b in tab}
 if len(tab)!=2*len(states) or any((q,b) not in tab for q in states for b in (0,1)):raise ValueError('incomplete')
 halts={t for w,d,t in tab.values()}-states
 if len(halts)!=1:raise ValueError('not unique halt')
 h=next(iter(halts));mapping={start:0};todo=collections.deque([start]);rows=[]
 while todo:
  q=todo.popleft()
  if q==h:continue
  for b in (0,1):
   w,d,t=tab[q,b]
   if t not in mapping:mapping[t]=len(mapping);todo.append(t)
   rows.append([mapping[q],b,w,d,mapping[t]])
 if set(mapping)!=states|halts:raise ValueError('unreachable control label')
 encoded=json.dumps(rows,separators=(',',':')).encode()
 return rows,mapping,hashlib.sha256(encoded).hexdigest()
def main():
 results={};classes=[];representatives={}
 for name,path in SELECTED.items():
  p=ROOT/'extracted'/path;tab=load_table(p);canonical,mapping,digest=canon(tab)
  if len(tab)!=416:raise ValueError('not 208 states')
  if digest not in representatives:classes.append(digest);representatives[digest]=name
  cl=chr(65+classes.index(digest))
  results[name]={'path':path,'working_states':208,'rows':416,'raw_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'canonical_sha256':digest,'class':cl,'canonical_map':mapping}
 if len(classes)!=2:raise ValueError('unexpected class count')
 (ROOT/'comparison_208.json').write_text(json.dumps({'method':'BFS, read 0 before read 1; writes and directions preserved; all labels reached','classes':representatives,'machines':results},indent=2)+'\n')
 for k,v in results.items():print(k,v['class'],v['raw_sha256'])
 print('Two classes confirmed by full rooted transition-graph isomorphism.')
if __name__=='__main__':main()
