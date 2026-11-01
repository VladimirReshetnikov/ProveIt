#!/usr/bin/env python3
"""Observe current workspace hashes against a frozen source capture; no replay."""
from pathlib import Path
import hashlib,json,subprocess
D=Path(__file__).resolve().parent;R=D.parents[3];M=D/'manifest.json';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();mh=H(M);sh=H(__file__);m=json.loads(M.read_text());head_before=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
def scan():
 out=[]
 for name,row in m['sources'].items():
  p=R/row['path'];actual=H(p) if p.is_file() else None
  if actual!=row['sha256']:out.append({'module':name,'expected':row['sha256'],'actual':actual})
 return out
a=scan();b=scan();head_after=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip();assert H(M)==mh and H(__file__)==sh
out={'status':'OBSERVED_WORKSPACE_DRIFT','manifest_sha256':mh,'checker_sha256':sh,'head_before':head_before,'head_after':head_after,'first':a,'second':b,'scope':'Two point-in-time workspace scans only; no source-current replay is claimed.'};p=D/'post-capture-drift.json';assert not p.exists();p.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(D.name,len(a),len(b),[x['module'] for x in b],H(p))
