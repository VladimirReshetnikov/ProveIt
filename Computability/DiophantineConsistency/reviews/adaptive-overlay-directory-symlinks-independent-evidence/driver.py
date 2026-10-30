"""Read-only directory-symlink inventory; no content/provenance assertion."""
from pathlib import Path
import hashlib,json,os,shutil,tempfile
roots={'canonical':'/tmp/adaptive13-assembly-recomposed-q9s50zdl','compat':'/tmp/adaptive-wang-table-compat-bu_4_5dx','reduced':'/tmp/adaptive-construction-reduced-zero-u6gt_026','model':'/tmp/adaptive-equivalence-client-55isyt4n','ha':'/tmp/ha-expression-assembly-vgttkwsl'};sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();statehash={k:sha(Path(p)/'state.json') for k,p in roots.items()};assert all(json.loads((Path(p)/'state.json').read_text())['status']=='PASS' for p in roots.values())
def scan():
 result={}
 for k,p in roots.items():
  lib=Path(p)/'lib';found=[]
  for d,dirs,files in os.walk(lib,followlinks=False):
   for n in dirs:
    q=Path(d)/n
    if q.is_symlink():found.append({'relative':str(q.relative_to(lib)),'target':str(q.resolve())})
  result[k]=sorted(found,key=lambda x:x['relative'])
 return result
first=scan();w=Path(tempfile.mkdtemp(prefix='adaptive-overlay-directory-symlinks-'));shutil.copyfile(__file__,w/'driver.py');result={'roots':roots,'provider_state_sha256':statehash,'directory_symlinks':first,'scope':'Directory-symlink paths only, without following symlinks; does not authenticate object contents, source ancestry, or provider compatibility.'};(w/'result.json').write_text(json.dumps(result,indent=2)+'\n');assert scan()==first and all(sha(Path(p)/'state.json')==statehash[k] for k,p in roots.items());state={'status':'PASS','private':str(w),'result_sha256':sha(w/'result.json'),'counts':{k:len(v) for k,v in first.items()},'scope':result['scope']};(w/'state.json').write_text(json.dumps(state,indent=2)+'\n');print('PASS',w,state['counts'],flush=True)
