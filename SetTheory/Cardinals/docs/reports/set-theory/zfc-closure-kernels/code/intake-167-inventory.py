"""Own read-only intake inventory of committed loop-rotation244 delivery and original placement history."""
from pathlib import Path,PurePosixPath
import subprocess,hashlib,json,zipfile,io,stat,re,collections
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');W=Path('/tmp/zfc244-d91a27b462-inspection');P=W/'zfc244-loop-rotation-20261018/zfc244-loop-rotation-20261018';OUT=W/'intake';OUT.mkdir(exist_ok=False)
def git(*args,raw=False):
 b=subprocess.check_output(['git','-C',str(R),*args]);return b if raw else b.decode()
def sha(b):return hashlib.sha256(b).hexdigest()
arrival=git('rev-parse','d91a27b462').strip();head=git('rev-parse','HEAD').strip();ap='docs/incoming/zfc244-loop-rotation-20261018.zip';raw=git('show',arrival+':'+ap,raw=True);assert raw==(R/ap).read_bytes();assert not git('status','--short','--','docs/incoming');oid=git('rev-parse',arrival+':'+ap).strip();members=[];seen=set()
with zipfile.ZipFile(io.BytesIO(raw)) as z:
 assert sum(i.file_size for i in z.infolist())<500_000_000
 for i in z.infolist():
  q=PurePosixPath(i.filename);assert q.parts and not q.is_absolute() and '..' not in q.parts and '\\' not in i.filename and ':' not in q.parts[0] and not stat.S_ISLNK(i.external_attr>>16);assert q not in seen;seen.add(q)
  if i.is_dir():continue
  b=z.read(i);p=P.parent.joinpath(*q.parts);assert p.read_bytes()==b and not p.is_symlink();members.append({'archive_member':i.filename,'relative':str(q.relative_to(P.name)),'path':str(p),'sha256':sha(b),'bytes':len(b)})
assert len(members)==1044
for j in range(0,len(members),100):
 rows=members[j:j+100];ids=git('hash-object','--no-filters','--',*[x['path'] for x in rows]).splitlines();assert len(ids)==len(rows)
 for x,h in zip(rows,ids):x['git_blob']=h
need={x['git_blob'] for x in members};hits={}
for line in git('rev-list','--objects','--all').splitlines():
 h,_,path=line.partition(' ')
 if h in need:hits.setdefault(h,[]).append(path)
for x in members:x['history_object_paths']=hits.get(x['git_blob'],[])
# A batched query is exactly the union of requested --find-object predicates;
# per-file raw diff identifiers preserve the matching object and commit.
cmd=['git','-C',str(R),'log','--all','--format=COMMIT%x09%H%x09%s','--raw','--no-renames','--abbrev=40',*[f'--find-object={x}' for x in sorted(hits)],'--']
r=subprocess.run(cmd,capture_output=True,text=True);assert r.returncode==0
(OUT/'find-object-output.txt').write_text(r.stdout);(OUT/'find-object-stderr.txt').write_text(r.stderr)
commits={};current=None
for line in r.stdout.splitlines():
 if line.startswith('COMMIT\t'):
  _,h,subject=line.split('\t',2);current=(h,subject)
 elif line.startswith(':'):
  left,_,path=line.partition('\t');f=left.split();assert current
  for h in f[2:4]:
   if h in need:commits.setdefault(h,[]).append({'commit':current[0],'subject':current[1],'path':path})
place={x['commit']:x['subject'] for xs in commits.values() for x in xs if re.search(r'\b(Place |Unpack, classify|Catalogue |Write batch|Merge batch)',x['subject'])}
# Check actual ancestor placement trees, not rewritten current files. Only
# placement-labelled commits establish original placement identities.
place={h:s for h,s in place.items() if re.search(r'^(Place |Unpack, classify)',s)}
trees=[]
for h,sub in sorted(place.items()):
 matches=[]
 for row in git('ls-tree','-r','-z',h).split('\0'):
  if not row:continue
  left,path=row.split('\t',1);mode,kind,blob=left.split()
  if blob in need:matches.append({'git_blob':blob,'path':path})
 trees.append({'commit':h,'subject':sub,'matching_members':matches})
record={'status':'SOURCE_ONLY_INTAKE_INVENTORY','head':head,'arrival':arrival,'archive':ap,'archive_blob':oid,'archive_sha256':sha(raw),'archive_bytes':len(raw),'extraction_validation':'Every committed member byte compared against root pristine tree; no extraction or supplied execution in this inventory.','members':members,'counts':{'members':len(members),'unique_git_blobs':len(need),'historically_present_unique_blobs':len(hits),'member_history_hits':sum(bool(x['history_object_paths']) for x in members),'original_placement_trees':len(trees)},'history_hits':commits,'placement_trees':trees,'first_main_files':[x for x in members if x['relative'] in ['report.tex','README.md','sections/rotation.tex','sections/formalisms.tex','code/verify_all.py','code/check_qt_rotation.py','code/make_qt244.py']],'supplied_execution':False,'checksum_manifest_work':False,'line_ending_work':False}
(OUT/'inventory.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'counts':record['counts'],'inventory_sha256':sha((OUT/'inventory.json').read_bytes()),'main_history':[(x['relative'],bool(x['history_object_paths'])) for x in record['first_main_files']]},indent=2))
