from pathlib import Path
import hashlib,json,re,shutil,subprocess
root=Path('/home/codex/.codex/worktrees/46be/Proofs');d=root/'Computability/DiophantineConsistency';p=Path('/tmp/foundation-ha-order-witnesses-gzwctvpw')
def sha(f):return hashlib.sha256(Path(f).read_bytes()).hexdigest()
def require(b,s):
 if not b:raise RuntimeError(s)
def check(f,h):require(sha(f)==h,'Pin drift '+str(f))
r=json.loads((p/'inputs.json').read_text());check(r['parent'],r['parent_sha256'])
for x in r['pins']:check(x['path'],x['sha256'])
for m in r['modules']:
 check(m['source'],m['source_sha256'])
 if 'trace' in m:check(m['trace'],m['trace_sha256'])
 for o in m.get('objects',[dict(path=m.get('object'),sha256=m.get('object_sha256'))]):check(o['path'],o['sha256'])
check(r['compiler']['path'],r['compiler']['sha256'])
for k,v in r['package_identity'].items():check(root/k,v['current_sha256'])
allruns=[json.loads(f.read_text())for f in sorted(p.glob('*-FoundationHAOrderWitnesses*.json'))]
require(len(allruns)==4,'Unexpected development runs')
for x in allruns:
 check(x['snapshot'],x['snapshot_sha256']);check(x['log'],x['log_sha256']);check('/tmp/foundation-ha-order-witnesses-build.py',x['driver_sha256'])
latest={x['module']:x for x in allruns};runs=[latest[k]for k in sorted(latest)];require(len(runs)==2,'Unexpected leaves')
for x in runs:
 require(x['exit_code']==0,'Unsuccessfulrun');check(x['source'],x['source_sha256']);check(x['snapshot'],x['snapshot_sha256']);check(x['log'],x['log_sha256']);check(x['object'],x['object_sha256']);check('/tmp/foundation-ha-order-witnesses-build.py',x['driver_sha256'])
 require(not re.search(r'error:|warning:|sorryAx',Path(x['log']).read_text()),'Diagnostics')
require(not Path(runs[0]['log']).read_bytes(),'Mainlog')
reports=re.findall(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",Path(runs[1]['log']).read_text(),re.S);require(len(reports)==24,'Reportcount')
for n,_,a in reports:require(set(x.strip()for x in a.split(',')if x.strip())<={'propext','Quot.sound','Classical.choice'},'Unexpectedaxiom')
bundle=d/'reviews/foundation-ha-order-witnesses-author-replay';bundle.mkdir(exist_ok=True)
files=list(p.glob('*.json'))+list(p.glob('*.lean'))+list(p.glob('*.log'))+[Path('/tmp/foundation-ha-order-witnesses-build.py'),Path(__file__)]
for f in files:shutil.copy2(f,bundle/f.name)
r.update(scope='Author validation, not independent review; two fresh leaves over95 source/object-authenticated prerequisites including76 Foundation modules. No prerequisite builds or frozen edits.',snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),private=str(p),fresh_modules=runs,development_runs=allruns,axiom_reports=[dict(theorem=n,axioms=[x.strip()for x in a.split(',')if x.strip()])for n,_,a in reports],bundle_files={f.name:sha(bundle/f.name)for f in sorted(files)},freeze_driver_sha256=sha(__file__))
out=d/'reviews/foundation-ha-order-witnesses-dependency-replay.json';out.write_text(json.dumps(r,indent=2)+'\n')
for x in runs:print(x['module'],len(Path(x['source']).read_text().splitlines()),x['source_sha256'],x['object_sha256'])
print('manifest',sha(out),'snapshot',r['snapshot'])
