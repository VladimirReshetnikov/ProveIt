#!/usr/bin/env python3
"""Own inert archive inventory/extraction. No supplied code, manifests or line-ending checks."""
from pathlib import Path,PurePosixPath
import subprocess,json,hashlib,zipfile,io,stat,re
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');W=Path('/tmp/zfc-intake-165-planning');E=W/'extracted';E.mkdir(exist_ok=False)
def git(*a,raw=False):
 v=subprocess.check_output(['git','-C',str(R),*a]);return v if raw else v.decode()
def desc(p):return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
head=git('rev-parse','HEAD').strip();st=git('status','--short','--','docs/incoming');assert not st,st
entries=[]
for row in git('ls-tree','-r','-z',head,'--','docs/incoming').split('\0'):
 if not row:continue
 left,path=row.split('\t',1);mode,kind,oid=left.split()
 if path.endswith('.zip'):entries.append((path,oid))
packages=[];allfiles=[]
for path,oid in entries:
 p=R/path;data=git('show',head+':'+path,raw=True);assert data==p.read_bytes()
 hist=git('log','--all','--diff-filter=A','--format=%H\t%aI\t%s','--',path).splitlines()
 assert hist
 arrival=hist[-1].split('\t',2)
 stem=Path(path).stem;out=E/stem;assert not out.exists();out.mkdir()
 with zipfile.ZipFile(io.BytesIO(data)) as z:
  infos=z.infolist();seen=set();members=[];total=sum(i.file_size for i in infos);assert total<500_000_000,(path,total)
  for i in infos:
   q=PurePosixPath(i.filename);assert '\\' not in i.filename and not q.is_absolute() and '..' not in q.parts and q.parts and ':' not in q.parts[0] and '\n' not in i.filename
   assert q not in seen,(path,str(q));seen.add(q)
   mode=i.external_attr>>16;assert not stat.S_ISLNK(mode),(path,str(q))
   target=out.joinpath(*q.parts)
   if i.is_dir():target.mkdir(parents=True,exist_ok=True);continue
   target.parent.mkdir(parents=True,exist_ok=True);payload=z.read(i);target.write_bytes(payload);row={'archive_member':i.filename,'path':str(target),'bytes':len(payload),'sha256':hashlib.sha256(payload).hexdigest()};members.append(row);allfiles.append((target,row))
 roots=sorted({PurePosixPath(i['archive_member']).parts[0] for i in members})
 packages.append({'archive':path,'archive_blob':oid,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'arrival_candidates':hist,'first_arrival':{'commit':arrival[0],'date':arrival[1],'subject':arrival[2]},'extraction':str(out),'members':members,'member_count':len(members),'uncompressed_bytes':total,'roots':roots})
for i in range(0,len(allfiles),100):
 batch=allfiles[i:i+100];hashes=git('hash-object','--no-filters','--',*[str(p) for p,_ in batch]).splitlines();assert len(hashes)==len(batch)
 for (_,row),h in zip(batch,hashes):row['git_blob']=h
# Global history object membership filters candidate duplicates; exact --find-object/placement-tree review follows separately.
history=git('rev-list','--objects','--all').splitlines();matches={};requested={q['git_blob'] for _,q in allfiles}
for line in history:
 h,_,path=line.partition(' ')
 if h in requested:matches.setdefault(h,[]).append(path)
for package in packages:
 for q in package['members']:q['history_object_paths']=matches.get(q['git_blob'],[])
 package['member_history_hits']=sum(bool(q['history_object_paths']) for q in package['members'])
packages.sort(key=lambda p:(p['first_arrival']['date'],p['archive']))
for n,p in enumerate(packages,1):p['queue_index']=n
result={'status':'SOURCE_ONLY_INVENTORY_NO_SUPPLIED_EXECUTION','repo':str(R),'head':head,'incoming_status':st,'normative_readme':desc(R/'docs/incoming/README.md'),'host_readme':desc(R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md'),'next_batch':165,'next_host_source':69,'archives':packages,'totals':{'archives':len(packages),'members':len(allfiles),'unique_git_blobs':len(requested),'historically_present_blobs':len(matches)},'history_scope':'Every extracted file hashed by git hash-object --no-filters. All-reachable-object membership checked; individual find-object and placement-tree checks follow. No checksum manifest or line-ending work.'}
(W/'inventory.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'totals':result['totals'],'archives':[{'n':p['queue_index'],'archive':p['archive'],'arrival':p['first_arrival']['commit'][:10],'members':p['member_count'],'history_hits':p['member_history_hits'],'roots':p['roots']} for p in packages]},indent=2))
