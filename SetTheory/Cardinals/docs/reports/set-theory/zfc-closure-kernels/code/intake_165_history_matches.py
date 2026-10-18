#!/usr/bin/env python3
"""Own Git-history metadata audit, no mutation or supplied-code execution."""
from pathlib import Path
import json,subprocess,re,hashlib,collections
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');W=Path('/tmp/zfc-intake-165-planning');I=json.loads((W/'inventory.json').read_text());hashes=sorted({q['git_blob'] for a in I['archives'] for q in a['members'] if q['history_object_paths']})
args=['git','-C',str(R),'log','--all','--raw','--no-renames','--no-abbrev','--format=COMMIT %H%x09%s',*[f'--find-object={h}' for h in hashes]]
p=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True);(W/'find-object-raw.txt').write_bytes(p.stdout);(W/'find-object-stderr.txt').write_bytes(p.stderr)
commits={};current=None;hits=collections.defaultdict(list)
for line in p.stdout.decode().splitlines():
 if line.startswith('COMMIT '):
  current,subject=line[7:].split('\t',1);commits[current]={'subject':subject,'rows':[]}
 elif line.startswith(':'):
  left,path=line.split('\t',1);parts=left.split();old,new=parts[2:4];d={'path':path,'old':old,'new':new,'status':parts[-1]};commits[current]['rows'].append(d)
  for h in {old,new}&set(hashes):hits[h].append({'commit':current,'subject':commits[current]['subject'],**d})
placement=[]
for commit,c in commits.items():
 if not re.search(r'\b(place|unpack, classify|unpack and catalogue)\b',c['subject'],re.I):continue
 paths=sorted({r['path'] for r in c['rows']});out=subprocess.check_output(['git','-C',str(R),'ls-tree','-r','-z',commit,'--',*paths]);members=[]
 for z in out.decode().split('\0'):
  if not z:continue
  left,path=z.split('\t',1);mode,kind,oid=left.split()
  if oid in hashes:members.append({'path':path,'git_blob':oid})
 placement.append({'commit':commit,'subject':c['subject'],'queried_paths':paths,'matching_tree_members':members})
# Exact resurfaced archive plus all273 original placements, independent of main files deliberately archived only.
archive='docs/incoming/zfc245-proof-20261018.zip';orig='8286787dd0468d848db345debe304b002d7064a4';place='46e8518e0eddc4bc16a7a1b38cd21bd58abf9226';data=subprocess.check_output(['git','-C',str(R),'show',orig+':'+archive]);cur=(R/archive).read_bytes();assert data==cur
package=next(a for a in I['archives'] if a['archive']==archive);source68=subprocess.check_output(['git','-C',str(R),'ls-tree','-r','-z',place,'--','SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels']).decode();match=[]
blobset={q['git_blob'] for q in package['members']}
for z in source68.split('\0'):
 if not z:continue
 left,path=z.split('\t',1);oid=left.split()[2]
 if '/68-' in path:assert oid in blobset,(path,oid);match.append({'path':path,'git_blob':oid})
assert len(match)==273,len(match)
result={'status':'HISTORY_AND_PLACEMENT_TREE_METADATA_AUDIT','inventory_sha256':hashlib.sha256((W/'inventory.json').read_bytes()).hexdigest(),'git_find_object_command':args,'find_object_unique_hashes':len(hashes),'hits':dict(hits),'placement_tree_checks':placement,'exact_reintroduced_archive':{'path':archive,'original_arrival':orig,'reintroduced_arrival':'8e1d867debff937dbf5345437fea67bc6db5430e','original_and_current_blob':'4f5f4bf61ab41a68221c50fef160ddc0cd27e0c1','original_bytes_equal_current':True,'original_placement':place,'all_273_ancillary_placement_blobs_equal_archive':True,'placement_members':match,'archive_only_main_delivery_files':21,'disposition':'Retire duplicate at next placement; do not assign a new local source.'},'limits':'All-reachable-object membership excludes5054-318 absent blobs; explicit repeated --find-object flags inspect318present blobs in one Git walk. Matching placement paths were confirmed in each original placement tree. Main source novelty also checked separately.'}
(W/'history-matches.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'history_hashes':len(hashes),'with_log_hits':len(hits),'placement_commits':len(placement),'duplicate273':len(match)},indent=2))
