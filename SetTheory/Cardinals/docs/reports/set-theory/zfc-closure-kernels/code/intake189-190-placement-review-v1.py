"""Own read-only Git/archive placement audit. No delivered code or manifest validation."""
from pathlib import Path
import subprocess,io,zipfile,json,hashlib,collections
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');O=Path('/tmp/zfc-catalogue189-190')
cat=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,cwd=R)
cache={}
def obj(ref):
 if ref not in cache:
  cat.stdin.write(ref.encode()+b'\n');cat.stdin.flush();h=cat.stdout.readline().split();assert len(h)==3,(ref,h);oid,kind,n=h;assert kind==b'blob',(ref,h);b=cat.stdout.read(int(n));assert cat.stdout.read(1)==b'\n';cache[ref]=(oid.decode(),b)
 return cache[ref]
def oid(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
head=git('rev-parse','HEAD').decode().strip();results=[]
for number,short in [(189,'d134378a07'),(190,'6ee648c500')]:
 commit=git('rev-parse',short).decode().strip();map_path=f'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake{number}-placement.json';mapoid,raw=obj(commit+':'+map_path);plan=json.loads(raw);assert (R/map_path).read_bytes()==raw
 counts=collections.Counter();new=set();retired=set();normalizations=[];sources=[]
 for s in plan['sources']:
  archive_oid,data=obj(s['arrival']+':'+s['archive']);assert archive_oid==s['archive_blob'] and len(data)==s['archive_bytes'];z=zipfile.ZipFile(io.BytesIO(data));names=[i.filename for i in z.infolist() if not i.is_dir()];members=s['members'];assert len(names)==len(set(names))==len(members);assert set(names)=={m['member'] for m in members}
  for m in members:
   b=z.read(m['member']);assert oid(b)==m['blob'] and len(b)==m['bytes'],m['member'];role=m['role'];counts[role]+=1
   if role=='archive-only':assert not m.get('target')
   elif role=='history-alias':
    h=m['history'];got,old=obj(h['commit']+':'+h['path']);assert got==h['blob']==m['blob'] and old==b
   else:
    target=m['target'];placed,contents=obj(commit+':'+target);current,now=obj(head+':'+target);assert contents==now==(R/target).read_bytes(),target
    if contents!=b:
     assert contents==b.replace(b'\r\n',b'\n'),target;normalizations.append({'source':s['source'],'member':m['member'],'target':target})
    assert placed==m.get('placed_blob',placed)
    if role=='new':new.add(target)
    elif role=='existing-alias':
     h=m['original_introduction'];got,old=obj(h['commit']+':'+h['path']);assert old==contents and got==h['blob'];assert h['placement'] is True
     oldcurrent,prev=obj(m['current_ref']+':'+target);assert prev==contents
    elif role=='batch-alias':assert any(n.get('target')==target and n['role']=='new' for t in plan['sources'] for n in t['members'])
    else:raise AssertionError(role)
  assert not git('ls-tree',commit,'--',s['archive']).strip(),s['archive'];retired.add(s['archive']);sources.append({'source':s['source'],'arrival':s['arrival'],'archive':s['archive'],'members':len(members),'arrival_archive_object':archive_oid})
 assert dict(counts)==plan['counts'];assert len(new)==plan['verification']['new_files'];assert sum(counts.values())==plan['verification']['members']
 changes=git('diff-tree','--no-commit-id','--name-status','-r',commit).decode().splitlines();adds={l[2:] for l in changes if l.startswith('A\t')};dels={l[2:] for l in changes if l.startswith('D\t')};assert adds==new|{map_path},(number,adds^(new|{map_path}));assert dels==retired;assert len(changes)==len(adds)+len(dels)
 result={'status':'INDEPENDENT_PLACEMENT_TREE_REVIEW_PASS','batch':number,'commit':commit,'current_head_checked':head,'sources':sources,'counts':dict(counts),'all_archive_members_bound':sum(counts.values()),'new_target_count':len(new),'all_target_bytes_match_original_or_existing_git_text_normalization':True,'original_introduction_trees_checked':True,'all_original_archives_retained_in_arrival_objects':True,'exact_commit_additions_and_zip_retirements_checked':True,'maximum_new_windows_length':max(len('C:\\ProveIt\\'+p.replace('/','\\')) for p in new),'git_text_normalizations':normalizations,'candidate_execution':False,'checksum_manifest_validation':False,'reviewer_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'map':{'path':map_path,'blob':mapoid},'findings':[]}
 (O/f'placement{number}-review.json').write_text(json.dumps(result,indent=2)+'\n');results.append({'batch':number,'status':result['status'],'members':sum(counts.values()),'new':len(new),'normalizations':len(normalizations)})
cat.stdin.close();cat.wait();print(json.dumps(results))
