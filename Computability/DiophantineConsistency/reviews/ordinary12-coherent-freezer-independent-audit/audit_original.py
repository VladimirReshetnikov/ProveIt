#!/usr/bin/env python3
"""Audit pinned original freezer and a recorded source snapshot; no build."""
import contextlib,hashlib,importlib.util,io,json,re,subprocess,sys,tempfile
from pathlib import Path
from unittest.mock import patch
if not __debug__:raise RuntimeError('assertions required')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';TASK=BASE/'research/ordinary12-ipra-bridge/difference-ring-build-plan/coherent-replay';EVID=TASK/'source-freeze-evidence';SNAP=Path('/tmp/ipra-ordinary12-coexistence-source-01');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
def git(commit,path):return subprocess.check_output(['git','show',commit+':'+str(path.relative_to(ROOT))],cwd=ROOT)
manifest=J(EVID/'manifest.json');obs=J(EVID/'observation.json');assert H(EVID/'manifest.json')=='a06785547271769030f3996dde2dd9180facfb751ea04608654abc6c37170ff4' and obs['freeze_exit_code']==obs['audit_exit_code']==0 and obs['status']=='SOURCE_FROZEN_NOT_COMPILED'
assert git('c86f587309',EVID/'manifest.json')==(EVID/'manifest.json').read_bytes()
rows=manifest['sources'];order=manifest['order'];assert len(rows)==len(order)==70 and len(set(order))==70 and len(manifest['external_modules'])==22 and manifest['status']=='FROZEN_NOT_COMPILED'
for path,key in [('lakefile.toml','lakefile_sha256'),('lean-toolchain','lean_toolchain_sha256')]:assert hashlib.sha256(subprocess.check_output(['git','show',manifest['head']+':'+path],cwd=ROOT)).hexdigest()==manifest[key]
for n,r in rows.items():
 raw=(SNAP/r['snapshot_path']).read_bytes();assert hashlib.sha256(raw).hexdigest()==r['sha256'] and git(manifest['head'],ROOT/r['workspace_path'])==raw
 deps=[m.group(1).decode() for m in re.finditer(rb'^import[ \t]+([^ \t\r\n]+)',raw,re.M)]
 assert deps==r['imports']
external={d for row in rows.values() for d in row['imports'] if d not in rows};assert external==set(manifest['external_modules'])
pos={n:i for i,n in enumerate(order)};assert all(pos[d]<pos[n] for n in order for d in rows[n]['imports'] if d in rows)
assert order[-1]=='DiophantineConsistency.FreeJProviderChecks';raw=(SNAP/rows[order[-1]]['snapshot_path']).read_text();reports=re.findall(r'^#print axioms (.+)$',raw,re.M);assert reports==['DiophantineConsistency.ModelDifferenceRing.internalZero_iff','FreeJNormZero.ordinary_residual_zero','FreeJNormZero.cleared_auxiliary_pairs'] and not re.search(r'^theorem ',raw,re.M)
original=git('3c47501313',TASK/'freeze.py');test=git('3c47501313',TASK/'test_freeze.py')
with tempfile.TemporaryDirectory(prefix='ipra-freezer-review-') as td:
 top=Path(td);fixture=top/'a/b/c/d/e/f';fixture.mkdir(parents=True);modpath=fixture/'freeze.py';modpath.write_bytes(original);(fixture/'test_freeze.py').write_bytes(test)
 p=subprocess.run([sys.executable,str(fixture/'test_freeze.py')],capture_output=True,text=True);assert p.returncode==0 and p.stdout.strip()=='PASS_COHERENT_FREEZER_TOY parser topology external cycle missing'
 spec=importlib.util.spec_from_file_location('freeze_original_review',modpath);f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
 fake=top/'fake-repository';fake.mkdir();(fake/'lakefile.toml').write_text('lean_lib = []\n');(fake/'lean-toolchain').write_text('toy\n');(fake/'Source.lean').write_text('def toy := 0\n');outside=top/'outside';outside.mkdir();(fake/'link').symlink_to(outside,target_is_directory=True)
 f.ROOT=fake;target=f.TARGET;names=['P.M'+str(i) for i in range(69)]+[target];blob=(fake/'Source.lean').read_bytes();fake_rows={n:{'path':'Source.lean','raw':blob,'imports':[]} for n in names}
 def walk(*args):return fake_rows,names,[]
 for label,dest in [('inside_checkout',fake/'created'),('symlinked_ancestor',fake/'link'/'created')]:
  with patch.object(f,'walk',walk),patch.object(f.subprocess,'check_output',return_value='fixture-head\n'),patch.object(sys,'argv',['freeze.py','--output',str(dest)]),contextlib.redirect_stdout(io.StringIO()):f.main()
  assert (dest/'manifest.json').is_file()
 assert (outside/'created/manifest.json').is_file()
report={'status':'PASS_INDEPENDENT_ORIGINAL_FREEZER_REVIEW','frozen_manifest_sha256':H(EVID/'manifest.json'),'frozen_head':manifest['head'],'sources':len(rows),'external_modules':len(manifest['external_modules']),'source_only':True,'toy_controls_exit':0,'original_inside_checkout_accepted':True,'original_symlinked_ancestor_accepted':True,'scope':'Original pre-correction output guard is insufficient; fake-root controls do not launch a project freeze or Lean build.'};out=HERE/'original-receipt.json'
if out.exists():raise ValueError('refusing overwrite')
out.write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(report['status'],H(out))
