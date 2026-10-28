from pathlib import Path
import hashlib,json,re,shutil,subprocess
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews';p=Path('/tmp/foundation-ha-peano-root-bhbxvn17')
def sha(f):return hashlib.sha256(Path(f).read_bytes()).hexdigest()
def check(f,h):assert sha(f)==h,str(f)
i=json.loads((p/'inputs.json').read_text())
for e in i['pins']:check(e['path'],e['sha256'])
check(i['compiler']['path'],i['compiler']['sha256'])
for n,e in i['package_identity'].items():check(R/n,e['current_sha256']);check(Path('/home/codex/src/Proofs')/n,e['cache_sha256'])
runs=[json.loads(f.read_text())for f in sorted(p.glob('*-FoundationHAPeano*.json'))];assert len(runs)==3 and[e['exit_code']for e in runs]==[0,1,0]
final=[runs[0],runs[2]]
for e in runs:
 check(e['snapshot'],e['snapshot_sha256']);check(e['log'],e['log_sha256']);check('/tmp/foundation-ha-peano-build.py',e['driver_sha256'])
for e in final:
 check(e['source'],e['source_sha256']);check(e['object'],e['object_sha256']);assert not re.search(r'error:|warning:|sorryAx',Path(e['log']).read_text())
assert not Path(final[0]['log']).read_bytes()
reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",Path(final[1]['log']).read_text());assert len(reports)==9
for n,a in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',a))<={'propext','Quot.sound','Classical.choice'},n
b=V/'foundation-ha-peano-author-replay';b.mkdir(exist_ok=True);files=[*p.glob('*.json'),*p.glob('*.lean'),*p.glob('*.log'),Path('/tmp/foundation-ha-peano-build.py'),Path(__file__)]
for f in files:shutil.copyfile(f,b/f.name)
d=dict(scope='Root author validation: two final fresh leaves over112 authenticated cached modules including85 Foundation modules. All three invocations retained; failed checks rejected. No fresh prerequisite closure.',snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),private=str(p),modules=i['modules'],compiler=i['compiler'],package_identity=i['package_identity'],fresh_modules=final,pin_observations=len(i['pins']),prior_manifests=i['parents'],authenticated_object_alternatives=i['authenticated_object_alternatives'],axiom_reports=reports,bundle_files={f.name:sha(b/f.name)for f in files},freeze_driver_sha256=sha(__file__))
out=V/'foundation-ha-peano-dependency-replay.json';out.write_text(json.dumps(d,indent=2)+'\n')
for e in final:print(e['module'],len(Path(e['source']).read_text().splitlines()),e['source_sha256'],e['object_sha256'])
print('manifest',sha(out),'reports',len(reports),'pins',len(i['pins']))
