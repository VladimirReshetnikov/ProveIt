"""Own source-only supplemental archive inventory; do not run delivered programs."""
from pathlib import Path,PurePosixPath
import subprocess,hashlib,json,zipfile,io,stat
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');W=Path('/tmp/zfc-intake-165-planning');O=W/'queue-supplement';O.mkdir(exist_ok=False)
def git(*args,raw=False):
 b=subprocess.check_output(['git','-C',str(R),*args]);return b if raw else b.decode()
sha=lambda b:hashlib.sha256(b).hexdigest()
old=json.loads((W/'inventory.json').read_text());known={x['archive'] for x in old['archives']};head=git('rev-parse','HEAD').strip();assert not git('status','--short','--','docs/incoming')
current=[];new=[]
for row in git('ls-tree','-r','-z',head,'--','docs/incoming').split('\0'):
 if not row:continue
 attrs,name=row.split('\t',1)
 if not name.endswith('.zip'):continue
 oid=attrs.split()[2];current.append({'path':name,'git_blob':oid})
 if name in known:continue
 raw=git('show',head+':'+name,raw=True);assert raw==(R/name).read_bytes();hist=git('log','--all','--diff-filter=A','--format=%H\t%aI\t%s','--',name).splitlines();arrival=hist[-1].split('\t',2)
 out=O/Path(name).stem;out.mkdir();members=[];seen=set()
 with zipfile.ZipFile(io.BytesIO(raw)) as z:
  assert sum(i.file_size for i in z.infolist())<500_000_000
  for i in z.infolist():
   q=PurePosixPath(i.filename);assert q.parts and not q.is_absolute() and '..' not in q.parts and '\\' not in i.filename and ':' not in q.parts[0] and '\n' not in i.filename and not stat.S_ISLNK(i.external_attr>>16);assert q not in seen;seen.add(q)
   if i.is_dir():continue
   b=z.read(i);p=out.joinpath(*q.parts);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);members.append({'archive_member':i.filename,'path':str(p),'bytes':len(b),'sha256':sha(b)})
 for j in range(0,len(members),100):
  rows=members[j:j+100];ids=git('hash-object','--no-filters','--',*[x['path'] for x in rows]).splitlines();assert len(ids)==len(rows)
  for x,h in zip(rows,ids):x['git_blob']=h
 new.append({'archive':name,'git_blob':oid,'sha256':sha(raw),'bytes':len(raw),'arrival':{'commit':arrival[0],'date':arrival[1],'subject':arrival[2]},'extraction':str(out),'member_count':len(members),'members':members,'review_status':'QUEUED_NOT_READ_OR_EXECUTED'})
assert len(current)==18 and len(new)==3
need={x['git_blob'] for p in new for x in p['members']};hits={}
for line in git('rev-list','--objects','--all').splitlines():
 h,_,path=line.partition(' ')
 if h in need:hits.setdefault(h,[]).append(path)
for p in new:
 for x in p['members']:x['history_object_paths']=hits.get(x['git_blob'],[])
 p['history_member_hits']=sum(bool(x['history_object_paths']) for x in p['members'])
record={'status':'SOURCE_ONLY_QUEUE_SUPPLEMENT','head':head,'historical_inventory':{'path':str(W/'inventory.json'),'sha256':sha((W/'inventory.json').read_bytes()),'archives':17},'retired':{'source69':'500381f8f1b4f450870895a642a2845a15a008ea','exact_source68_repeat':'500381f8f1b4f450870895a642a2845a15a008ea'},'current_pending_count':18,'current_pending':current,'new_arrivals':new,'history_scope':'Every new member hashed; exact reachable Git-object membership checked. Individual find-object and original placement-tree classification deferred until these queued manuscripts are selected. No duplicate or novelty disposition inferred.','supplied_execution':False,'checksum_manifest_verification':False}
(O/'queue-supplement.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'head':head,'pending':len(current),'new':[{'archive':p['archive'],'members':p['member_count'],'hits':p['history_member_hits']} for p in new],'record_sha256':sha((O/'queue-supplement.json').read_bytes())},indent=2))
