#!/usr/bin/env python3
"""Two point-in-time workspace scans against the running frozen replay."""
from pathlib import Path
import hashlib,json,subprocess
D=Path(__file__).resolve().parent;V=D.parent;R=D.parents[3];M=V/'ipra-current-repaired-post120-replay/manifest.json';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();mh=H(M);sh=H(__file__);m=json.loads(M.read_text());assert len(m['workspace_sources'])==1104
head0=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
def scan():
 out=[]
 for name,row in m['workspace_sources'].items():
  p=R/row['path'];actual=H(p) if p.is_file() else None
  if actual!=row['sha256']:out.append({'module':name,'expected':row['sha256'],'actual':actual})
 return out
a=scan();b=scan();head1=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip();assert H(M)==mh and H(__file__)==sh
out={'status':'OBSERVED_WORKSPACE_DRIFT','manifest_sha256':mh,'checker_sha256':sh,'head_before':head0,'head_after':head1,'first':a,'second':b,'scope':'Point-in-time workspace observation only; the frozen replays continue independently.'};p=D/'receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],len(a),len(b),[x['module'] for x in b],H(p))
