#!/usr/bin/env python3
"""Independently rehash corrected-freezer source snapshot and current workspace."""
import hashlib,json,re,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('assertions required')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];SNAP=Path('/tmp/ipra-ordinary12-coexistence-source-02');SOURCE_AUDIT=Path('/tmp/ipra-ordinary12-coexistence-source-audit-02.json');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
def git(c,p):return subprocess.check_output(['git','show',c+':'+p],cwd=ROOT)
def head():return subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
assert H(SNAP/'manifest.json')=='de7da3da7cd29b9d65e441d5141c8da3d604bd4ce861182b4d41d21fbc39df25' and H(SOURCE_AUDIT)=='a2ee8125262c815350e32337342539e39820d33f54c54fcb2b87265ccfb52cd5'
m=J(SNAP/'manifest.json');a=J(SOURCE_AUDIT);now=head();assert a['status']=='PASS_SOURCE_SNAPSHOT_AUDIT' and a['manifest_sha256']==H(SNAP/'manifest.json') and a['current_HEAD']==m['head'] and not a['changed_against_current_HEAD'] and not a['untracked']
rows=m['sources'];order=m['order'];assert m['status']=='FROZEN_NOT_COMPILED' and len(rows)==len(order)==70 and len(set(order))==70 and len(m['external_modules'])==22
for path,key in [('lakefile.toml','lakefile_sha256'),('lean-toolchain','lean_toolchain_sha256')]:assert hashlib.sha256(git(m['head'],path)).hexdigest()==m[key] and H(ROOT/path)==m[key]
for n,row in rows.items():
 raw=(SNAP/row['snapshot_path']).read_bytes();path=row['workspace_path'];assert hashlib.sha256(raw).hexdigest()==row['sha256'] and raw==git(m['head'],path)==git(now,path)==(ROOT/path).read_bytes()
 assert [x.group(1).decode() for x in re.finditer(rb'^import[ \t]+([^ \t\r\n]+)',raw,re.M)]==row['imports']
assert {d for row in rows.values() for d in row['imports'] if d not in rows}==set(m['external_modules'])
pos={n:i for i,n in enumerate(order)};assert order[-1]=='DiophantineConsistency.FreeJProviderChecks' and all(pos[d]<pos[n] for n in order for d in rows[n]['imports'] if d in rows)
assert head()==now
out=HERE/'snapshot2-receipt.json';result={'status':'PASS_INDEPENDENT_CORRECTED_FREEZE_SOURCE_AUDIT','manifest_sha256':H(SNAP/'manifest.json'),'producer_audit_sha256':H(SOURCE_AUDIT),'frozen_head':m['head'],'independent_head':now,'project_modules':len(rows),'external_imports':len(m['external_modules']),'workspace_and_head_drift':[],'scope':'Point-in-time pinned source/header survey; no compiler-resolved import graph, Lean build, package/dynamic ancestry or iPRA theorem.'}
if out.exists():raise ValueError('refusing overwrite')
out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(result['status'],H(out))
