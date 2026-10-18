#!/usr/bin/env python3
"""Recover source69 and compare all454 placed ancillary bytes; no suites/builds."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,io,json,stat,subprocess,zipfile
MAP_SHA='c07a9154bf8d11513e6c57a94583366371945d938470d59e23d881b4f942a71e'
HOST=Path('SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels')
def sha(b):return hashlib.sha256(b).hexdigest()
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--map',type=Path);a=ap.parse_args();repo=a.repo.resolve();output=a.output.resolve();mp=a.map or repo/HOST/'data/intake-165-placement.json';assert not output.exists() and output!=repo and repo not in output.parents;assert sha(mp.read_bytes())==MAP_SHA;plan=json.loads(mp.read_text());arc=plan['archive'];raw=subprocess.check_output(['git','-C',str(repo),'show',arc['first_arrival']['commit']+':'+arc['archive']]);assert sha(raw)==arc['sha256'];files={}
with zipfile.ZipFile(io.BytesIO(raw)) as z:
 assert sum(i.file_size for i in z.infolist())<500_000_000
 for i in z.infolist():
  p=PurePosixPath(i.filename);assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename and ':' not in p.parts[0] and '\n' not in i.filename and not stat.S_ISLNK(i.external_attr>>16)
  if i.is_dir():continue
  assert i.filename not in files;files[i.filename]=z.read(i)
assert len(files)==466;compared=0
for row in plan['files']:
 b=files[row['archive_member']];assert sha(b)==row['sha256']
 if row['disposition']=='place_unchanged':assert (repo/row['target']).read_bytes()==b;compared+=1
assert compared==454
output.mkdir()
for member,b in files.items():
 p=output.joinpath(*PurePosixPath(member).parts);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
root=output/'zfc-sub246-research-20261018';record={'status':'RECOVERED_AND_PLACED_BYTES_MATCH','archive':arc,'files_recovered':466,'placed_pairs_compared':454,'package_root':str(root),'supplied_execution':False,'checksum_manifest_verification':False};(output/'recovery.json').write_text(json.dumps(record,indent=2)+'\n');print(root);print(json.dumps({'status':record['status'],'files':466,'placed_pairs':454}))
