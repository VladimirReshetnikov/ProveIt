#!/usr/bin/env python3
"""Independently rehash corrected-freezer source-03 snapshot and current workspace."""
import hashlib,json,re,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('assertions required')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];SNAP=Path('/tmp/ipra-ordinary12-coexistence-source-03');SOURCE_AUDIT=Path('/tmp/ipra-ordinary12-coexistence-source-audit-03.json');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
def git(c,p):return subprocess.check_output(['git','show',c+':'+p],cwd=ROOT)
def head():return subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
assert H(SNAP/'manifest.json')=='9a7059e439bb77ab258808789fd1165cff8a4961c609e132ca0ed2130cb27ded' and H(SOURCE_AUDIT)=='62fe3d1f2fee807ba3a81a32b8f8b4c6e918635e2a64fbd028596533dbcd9631'
m=J(SNAP/'manifest.json');a=J(SOURCE_AUDIT);now=head();assert a['status']=='PASS_SOURCE_SNAPSHOT_AUDIT' and a['manifest_sha256']==H(SNAP/'manifest.json') and a['current_HEAD']==m['head'] and not a['changed_against_current_HEAD'] and not a['untracked']
EVID=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/difference-ring-build-plan/coherent-replay/source-freeze-evidence-03';FREEZER=EVID.parent/'freeze.py'
for name in ('manifest.json','audit.json','observation.json'):
 p=EVID/name;assert git('7274110bb1',str(p.relative_to(ROOT)))==p.read_bytes()
assert H(EVID/'manifest.json')==H(SNAP/'manifest.json') and H(EVID/'audit.json')==H(SOURCE_AUDIT)
obs=J(EVID/'observation.json');assert obs['freeze_exit_code']==obs['audit_exit_code']==0 and obs['freezer_git_commit']=='d8e97ac5fc' and obs['freezer_sha256']=='371a883c2997db3abbf7711473218d7fcee8b050245aef41736abaf04ef9f9d8'
assert hashlib.sha256(git('d8e97ac5fc',str(FREEZER.relative_to(ROOT)))).hexdigest()==obs['freezer_sha256'] and hashlib.sha256(git(m['head'],str(FREEZER.relative_to(ROOT)))).hexdigest()==obs['freezer_sha256']
rows=m['sources'];order=m['order'];assert m['status']=='FROZEN_NOT_COMPILED' and len(rows)==len(order)==70 and len(set(order))==70 and len(m['external_modules'])==22
for path,key in [('lakefile.toml','lakefile_sha256'),('lean-toolchain','lean_toolchain_sha256')]:assert hashlib.sha256(git(m['head'],path)).hexdigest()==m[key] and H(ROOT/path)==m[key]
for n,row in rows.items():
 raw=(SNAP/row['snapshot_path']).read_bytes();path=row['workspace_path'];assert hashlib.sha256(raw).hexdigest()==row['sha256'] and raw==git(m['head'],path)==git(now,path)==(ROOT/path).read_bytes()
 assert [x.group(1).decode() for x in re.finditer(rb'^import[ \t]+([^ \t\r\n]+)',raw,re.M)]==row['imports']
assert {d for row in rows.values() for d in row['imports'] if d not in rows}==set(m['external_modules'])
pos={n:i for i,n in enumerate(order)};assert order[-1]=='DiophantineConsistency.FreeJProviderChecks' and all(pos[d]<pos[n] for n in order for d in rows[n]['imports'] if d in rows)
assert head()==now
out=HERE/'receipt.json';result={'status':'PASS_INDEPENDENT_COHERENT_SOURCE03_AUDIT','manifest_sha256':H(SNAP/'manifest.json'),'producer_audit_sha256':H(SOURCE_AUDIT),'frozen_head':m['head'],'independent_head':now,'project_modules':len(rows),'external_imports':len(m['external_modules']),'workspace_and_head_drift':[],'scope':'Point-in-time pinned source/header survey; no compiler-resolved import graph, Lean build, package/dynamic ancestry or iPRA theorem.'}
if out.exists():raise ValueError('refusing overwrite')
out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(result['status'],H(out))
