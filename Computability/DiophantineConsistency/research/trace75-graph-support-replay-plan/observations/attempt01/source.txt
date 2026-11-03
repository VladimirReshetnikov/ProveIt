#!/usr/bin/env python3
"""Read-only captured-header replay planning; no Lean and no provider mutation."""
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
import heapq,json,re,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1];R=D/'research'
TRIAGE=R/'trace75-graph-support-28-triage/observations/attempt01/stdout'
SEVEN=R/'trace75-graph-support-seven-observations/observations/attempt01/stdout'
PACK=R/'trace75-packing-blocks-observation/observations/attempt01/stdout'
FINAL=R/'trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json'
PINS={TRIAGE:'a1f701226ce2c5c1f9eef7b627f4d6ce6aa494bc4689c846d8617f172d750570',
      SEVEN:'8f6360726fe0f1917da33d3914c91d09e30b9c71402a20d6758ad1aa5d9f03f9',
      PACK:'c2a15eac221a02abca6144f122089d88c607112dc3391a2c9885a9135111d654',
      FINAL:'b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c'}
def need(b,m):
    if not b:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
for p,h in PINS.items():need(sha(p)==h,'input drift '+str(p))
triage=json.loads(TRIAGE.read_text());seven=json.loads(SEVEN.read_text());pack=json.loads(PACK.read_text());final=json.loads(FINAL.read_text())
need(all(x['status']=='PASS' for x in [triage,seven,pack,final]),'input status')
rows={r['module']:r for r in triage['records']};nodes=set(rows);need(len(nodes)==28,'node count')
headers=final['serialized_headers'];project=set(final['selected_project']);outside=set(final['selected_outside'])
indegree={};reverse=defaultdict(set);upstream=set();external=set();internal=0
for n in nodes:
    imports=set(headers[n]);deps=imports&nodes;indegree[n]=len(deps);internal+=len(deps)
    for d in deps:reverse[d].add(n)
    upstream|=(imports-nodes)&project;external|=(imports-nodes)&outside
    need(imports<=nodes|project|outside,'unresolved input '+n)
ready=[n for n in nodes if indegree[n]==0];heapq.heapify(ready);order=[]
while ready:
    n=heapq.heappop(ready);order.append(n)
    for user in sorted(reverse[n]):
        indegree[user]-=1
        if indegree[user]==0:heapq.heappush(ready,user)
need(len(order)==28,'captured header graph cyclic')
seven_names={r['module'] for r in seven['records']};need(len(seven_names)==7,'seven observations changed')
records=[];seen_sources={}
for n in order:
    row=rows[n]
    if row['overlay_source']:
        need(len(row['workspace_matches'])==1,'source candidate ambiguity '+n)
        source=Path(row['workspace_matches'][0]);expected=row['overlay_source']['sha256'];category='current source equals overlay-root source'
    else:
        need(n=='DiophantineConsistency.ArithmeticPackingBlocks','unexpected missing overlay source')
        source=R/'ordinary12-ipra-bridge/compact44-represented-orbit-word-prototype/evidence/ArithmeticPackingBlocks.lean'
        expected=pack['reported_source_sha256'];category='retained reported source; no overlay-root source'
    need(source.is_file() and sha(source)==expected,'candidate source drift '+n);seen_sources[str(source)]=expected
    text=source.read_text();imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',text,re.M)
    need(imports==[x for x in headers[n] if x!='Init'],'source/header mismatch '+n)
    reports=re.findall(r'^\s*#print\s+axioms\s+([^\s]+)',text,re.M)
    need(all(re.fullmatch(r'[A-Za-z0-9_.]+',x) for x in reports),'unexpected report syntax '+n)
    records.append({'module':n,'source':str(source),'source_sha256':expected,'source_category':category,
      'captured_header':headers[n],'print_axioms_source_tokens':reports,
      'has_reported_source_session':n in seven_names or n=='DiophantineConsistency.ArithmeticPackingBlocks',
      'overlay_log_candidates':row['overlay_logs']})
def selected_record(n):
    r=final['selected_project'].get(n) or final['selected_outside'].get(n);need(r is not None,'selected object absent '+n)
    for item in r.values():
        if item is None:continue
        p=Path(item['path']);need(p.is_file() and str(p.resolve())==item['resolved'] and sha(p)==item['sha256'],'selected companion drift '+n)
    return {'module':n,'olean_realpath':r['.olean']['resolved'],'olean_sha256':r['.olean']['sha256']}
project_inputs=[selected_record(n) for n in sorted(upstream)];outside_inputs=[selected_record(n) for n in sorted(external)]
all_project=set(final['closures']['Trace75BFSFixedIPRA']['project']);users=defaultdict(set)
for n in all_project:
    for d in headers[n]:
        if d in all_project:users[d].add(n)
affected=set(nodes);todo=list(nodes)
while todo:
    for n in users[todo.pop()]:
        if n not in affected:affected.add(n);todo.append(n)
need('Trace75BFSFixedIPRA' in affected,'fixed endpoint not downstream')
for p,h in PINS.items():need(sha(p)==h,'input changed '+str(p))
for p,h in seen_sources.items():need(sha(p)==h,'candidate source changed '+p)
print(json.dumps({'status':'PASS','order':order,'sources':records,'internal_edges':internal,
 'direct_project_inputs':project_inputs,'direct_outside_inputs':outside_inputs,'reverse_reachable':sorted(affected),
 'summary':{'nodes':len(nodes),'internal_edges':internal,'direct_project_inputs':len(upstream),'direct_outside_inputs':len(external),
  'source_axiom_directives':sum(len(r['print_axioms_source_tokens']) for r in records),
  'sources_with_reported_sessions':sum(r['has_reported_source_session'] for r in records),'reverse_reachable':len(affected)},
 'scope':'captured-header order and candidate source planning only; no producer authentication, new Lean run or full endpoint replay'},sort_keys=True))
