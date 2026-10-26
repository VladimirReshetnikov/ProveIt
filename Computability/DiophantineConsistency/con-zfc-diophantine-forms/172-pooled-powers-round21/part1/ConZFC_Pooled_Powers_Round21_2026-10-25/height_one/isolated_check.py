import hashlib,json,shutil,subprocess,sys
from pathlib import Path
here=Path(__file__).resolve().parent;out=here/'isolated_release';out.mkdir(exist_ok=True)
wl=json.loads((here/'RELEASE_WHITELIST.json').read_text())['files'];omitted={'ISOLATED_REPLAY.json','REPLAY_BOTH.json','MANIFEST_SHA256.json'}
for f in wl:
 if f in omitted:continue
 p=out/f;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(here/f,p)
def dg(p):return hashlib.sha256(p.read_bytes()).hexdigest()
cfg=json.loads((out/'CONFIG.json').read_text());targets=['ENDPOINTS.json']
for p in cfg['profiles']:targets += ['endpoints/'+p['name']+'/'+f for f in ['polynomial.json','certificate.json','metrics.json','polynomial.txt']]
for p in cfg['sources'].values():targets += [p['refactored']+'/source.json',p['refactored']+'/factor_certificate.json']
before={f:dg(out/f) for f in targets}
subprocess.run([sys.executable,'-O','build.py'],cwd=out,check=True,text=True,capture_output=True)
after={f:dg(out/f) for f in targets}
if before!=after:raise ValueError('isolated deterministic build mismatch')
cp=subprocess.run([sys.executable,'-O','verify.py','--single','--skip-rebuild'],cwd=out,check=True,text=True,capture_output=True);audit=json.loads(cp.stdout)
result={'status':'pass','copied_only_release_whitelist':True,'omitted_non_input_reports_and_manifest':sorted(omitted),'isolated_optimized_build':'byte_identical','regenerated_files':before,'independent_optimized_audit':audit}
(here/'ISOLATED_REPLAY.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':result['status'],'files_rebuilt':len(targets),'endpoints':len(audit['endpoints'])}))
