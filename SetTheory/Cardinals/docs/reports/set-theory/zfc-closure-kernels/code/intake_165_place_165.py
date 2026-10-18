#!/usr/bin/env python3
"""Root-run batch165 placement: fresh committed bytes, no supplied code or Git mutations.
The caller stages files and retires only the two named ZIPs in one placement commit.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,io,json,stat,subprocess,zipfile
PLAN_SHA='c07a9154bf8d11513e6c57a94583366371945d938470d59e23d881b4f942a71e'
HISTORY_SHA='0aa992b40791e2a431ab02a71c86277fa5a2b6f85155ac8b39cd5b918a10553b'
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def git(repo,*args):return subprocess.check_output(['git','-C',str(repo),*args])
def payloads(raw):
 out={}
 with zipfile.ZipFile(io.BytesIO(raw)) as z:
  assert sum(i.file_size for i in z.infolist())<500_000_000
  for i in z.infolist():
   p=PurePosixPath(i.filename);assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename and ':' not in p.parts[0] and '\n' not in i.filename and not stat.S_ISLNK(i.external_attr>>16)
   if i.is_dir():continue
   assert i.filename not in out;out[i.filename]=z.read(i)
 return out
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--map',type=Path,default=Path(__file__).with_name('placement-proposal.json'));ap.add_argument('--history',type=Path,default=Path(__file__).with_name('history-matches.json'));a=ap.parse_args();repo=a.repo.resolve();output=a.output.resolve();assert repo not in output.parents and output!=repo and not output.exists()
assert sha(a.map.read_bytes())==PLAN_SHA and sha(a.history.read_bytes())==HISTORY_SHA;plan=json.loads(a.map.read_text());hist=json.loads(a.history.read_text());arc=plan['archive'];raw=git(repo,'show',arc['first_arrival']['commit']+':'+arc['archive']);assert sha(raw)==arc['sha256'] and blob(raw)==arc['archive_blob'];assert (repo/arc['archive']).read_bytes()==raw
files=payloads(raw);assert len(files)==466
for row in plan['files']:
 b=files[row['archive_member']];assert sha(b)==row['sha256'] and blob(b)==row['git_blob'] and len(b)==row['bytes']
 if row['disposition']=='place_unchanged':
  dest=repo/row['target'];assert repo in dest.resolve().parents and not dest.exists(),dest
# Independent exact duplicate retirement evidence from original source68 tree.
dup=hist['exact_reintroduced_archive'];old=git(repo,'show',dup['original_arrival']+':'+dup['path']);assert old==(repo/dup['path']).read_bytes() and blob(old)==dup['original_and_current_blob'];original68={blob(b) for b in payloads(old).values()}
for row in dup['placement_members']:
 b=git(repo,'show',dup['original_placement']+':'+row['path']);assert blob(b)==row['git_blob'] and row['git_blob'] in original68
assert len(dup['placement_members'])==273
output.mkdir();fresh=output/'fresh-extraction';fresh.mkdir();written=[]
for member,b in files.items():
 p=fresh.joinpath(*PurePosixPath(member).parts);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
for row in plan['files']:
 if row['disposition']!='place_unchanged':continue
 src=fresh.joinpath(*PurePosixPath(row['archive_member']).parts);dest=repo/row['target'];dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(src.read_bytes());assert blob(dest.read_bytes())==row['git_blob'];written.append(row['target'])
assert len(written)==454
(output/'stage-paths.txt').write_text('\n'.join(written)+'\n');(output/'retire-paths.txt').write_text('\n'.join(plan['retire_only_after_exact_placement'])+'\n')
record={'status':'PLACED_BYTES_VERIFIED_NOT_STAGED_OR_COMMITTED','map_sha256':PLAN_SHA,'history_sha256':HISTORY_SHA,'repo_head':git(repo,'rev-parse','HEAD').decode().strip(),'source_members':466,'placed':454,'archive_only':12,'duplicate_original273_verified':True,'written':written,'retire_only_after_staging_exact_files':plan['retire_only_after_exact_placement'],'fresh_extraction':str(fresh),'proof_or_supplied_execution':False,'git_mutations':False}
(output/'placement.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'status':record['status'],'placed':len(written),'output':str(output)}))
