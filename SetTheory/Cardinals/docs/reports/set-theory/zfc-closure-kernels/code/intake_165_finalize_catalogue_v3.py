"""Freeze scratch catalogue texts with an actual write commit; no build/repo mutation."""
from pathlib import Path
import argparse,hashlib,json,subprocess,difflib
P=Path('/tmp/zfc-intake-165-planning/catalogue-preview-v3')
MAP_SHA='be6a03b8a47b45821d2d9e74d1f9bffa5ba14b8f82f633c8e5ddb95fbd884ef5'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--write-sha',required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();R=a.repo.resolve();O=a.output.resolve();assert not O.exists() and not O.is_relative_to(R)
M=P/'replacement-map.json';assert sha(M)==MAP_SHA;m=json.loads(M.read_text());commit=subprocess.check_output(['git','-C',str(R),'rev-parse',a.write_sha+'^{commit}']).decode().strip();assert len(commit)==40
rows=[];patch=[];O.mkdir()
for x in m['files']:
 src=Path(x['replacement']);assert sha(src)==x['after_sha256'];before=R/x['target'];assert sha(before)==x['before_sha256'];old=before.read_text();new=src.read_text().replace('WRITE165SHA',commit[:10]);dst=O/'files'/x['target'];dst.parent.mkdir(parents=True,exist_ok=True);dst.write_text(new);rows.append({'target':x['target'],'replacement':str(dst),'before_sha256':x['before_sha256'],'after_sha256':sha(dst)});patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=x['target'],tofile=x['target']))
(O/'catalogue.patch').write_text(''.join(patch));m.update(status='FINAL_SOURCE_ONLY_READY_FOR_ROOT_AUDIT_AND_BUILD',write=commit,files=rows,patch_sha256=sha(O/'catalogue.patch'));(O/'replacement-map.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps(m,indent=2))
