"""Freeze catalogue166 with actual write commit; no build or repository mutation."""
from pathlib import Path
import argparse,hashlib,json,subprocess,difflib
P=Path('/tmp/zfc244-248bc05936-inspection/intake/catalogue-preview-v2')
MAP_SHA='acf0c41de91c0ea12ff41d9a7716745d2a76523053916ef690562ee9f24b4627'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True)
p.add_argument('--write-sha',required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args();R=a.repo.resolve();O=a.output.resolve()
assert __debug__ and not O.exists() and not O.is_relative_to(R)
M=P/'replacement-map.json';assert sha(M)==MAP_SHA
m=json.loads(M.read_text());commit=subprocess.check_output(['git','-C',str(R),'rev-parse',a.write_sha+'^{commit}']).decode().strip()
assert commit=='be13ec69d7e74fd69674966e4c88698400e4066f'
rows=[];patch=[];O.mkdir()
for x in m['files']:
 src=Path(x['replacement']);assert sha(src)==x['after_sha256'];before=R/x['target'];assert sha(before)==x['before_sha256']
 old=before.read_text();new=src.read_text().replace('WRITE166SHA',commit[:10]);dst=O/'files'/x['target'];dst.parent.mkdir(parents=True,exist_ok=True);dst.write_text(new)
 rows.append({'target':x['target'],'replacement':str(dst),'before_sha256':x['before_sha256'],'after_sha256':sha(dst)})
 patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=x['target'],tofile=x['target']))
(O/'catalogue.patch').write_text(''.join(patch));m.update(status='FINAL_SOURCE_ONLY_READY_FOR_ROOT_AUDIT_AND_BUILD',write=commit,files=rows,patch_sha256=sha(O/'catalogue.patch'))
(O/'replacement-map.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps(m,indent=2))
