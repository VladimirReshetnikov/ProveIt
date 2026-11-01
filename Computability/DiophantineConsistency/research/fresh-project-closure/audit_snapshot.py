#!/usr/bin/env python3
"""Audit frozen/current source equality and Git index membership; no Lean replay."""
import argparse,hashlib,json,subprocess
from pathlib import Path
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=argparse.ArgumentParser();p.add_argument('snapshot',type=Path);p.add_argument('--output',type=Path);a=p.parse_args();snap=a.snapshot.resolve(strict=True);m=json.loads((snap/'manifest.json').read_text());root=Path(m['root']);names=m['order'];assert len(set(names))==m['project_modules']==len(m['sources']);seen=set()
for n in names:
 row=m['sources'][n]
 assert all(dep not in m['sources'] or dep in seen for dep in row['imports']),('ordering',n)
 assert H(root/row['workspace_path'])==H(snap/row['snapshot_path'])==row['sha256'],('source mismatch',n)
 seen.add(n)
paths=[m['sources'][n]['workspace_path'] for n in names]
def gitlist(*args):return {x.decode() for x in subprocess.check_output(['git',*args,'--',*paths],cwd=root).split(b'\0') if x}
tracked=gitlist('ls-files','-z');changed=gitlist('diff','--name-only','-z','HEAD');untracked=set(paths)-tracked
out={'status':'PASS_SOURCE_SNAPSHOT_AUDIT' if not untracked and not changed else 'SOURCE_INDEX_DRIFT','manifest_sha256':H(snap/'manifest.json'),'snapshot':str(snap),'project_modules':len(names),'external_imports':len(m['external_modules']),'untracked':sorted(untracked),'changed_against_current_HEAD':sorted(changed),'current_HEAD':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'scope':'Point-in-time source bytes, topological order and Git membership/diff only; line-based import discovery is not authoritative Lean parsing, and no build or package-transitive/dynamic provenance is established.'}
p=a.output.absolute() if a.output else snap/'source-audit.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],H(p),'tracked',len(tracked),'changed',len(changed),'untracked',len(untracked),flush=True)
if out['status']!='PASS_SOURCE_SNAPSHOT_AUDIT':raise SystemExit(1)
