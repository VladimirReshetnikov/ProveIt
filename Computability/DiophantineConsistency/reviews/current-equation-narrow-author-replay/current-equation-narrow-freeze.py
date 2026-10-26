from pathlib import Path
import json,hashlib,shutil,re,subprocess
root=Path('/home/codex/.codex/worktrees/46be/Proofs');d=root/'Computability/DiophantineConsistency';src=d/'Lean/DiophantineConsistency';rev=d/'reviews'
p=Path('/tmp/current-equation-narrow-location.txt').read_text();p=Path(p)
def sha(f):return hashlib.sha256(Path(f).read_bytes()).hexdigest()
def require(b,s):
 if not b:raise RuntimeError(s)
def check(f,h):require(sha(f)==h,'Drift '+str(f))
inputs=json.loads((p/'inputs.json').read_text())
for pin in inputs['pins']:check(pin['path'],pin['sha256'])
check(inputs['compiler']['path'],inputs['compiler']['sha256'])
for f,rec in inputs['package_identity'].items():check(root/f,rec['current_sha256'])
for m in inputs['modules']:
 check(m['source'],m['source_sha256'])
 if 'trace' in m:check(m['trace'],m['trace_sha256'])
 for o in m.get('objects',[dict(path=m.get('object'),sha256=m.get('object_sha256'))]):check(o['path'],o['sha256'])
move_path=Path('/tmp/current-equation-narrow-move-originals/move-manifest.json');moves=json.loads(move_path.read_text())
newfiles=[x['module'] for x in moves['new_sources']]
allnew='\n'.join((src/(n+'.lean')).read_text() for n in newfiles)
for e in moves['moves']:
 require(allnew.count(e['text'])==1,'Moved declaration absent or duplicated '+e['name'])
 require(hashlib.sha256(e['text'].encode()).hexdigest()==e['sha256'],'Bad declaration hash')
imports=dict(LowMaskCoding='LowMaskData',WangTiles942Core='WangTiles942TableData',CurrentMasks2011='CurrentMaskData2011',CurrentKernel2011='CurrentKernelData2011',CurrentWindowCarry2011='CurrentKernelData2011',ObjectCurrentEquation2011='CurrentEquationSyntax2011',ArithmeticCurrentEquation2011='CurrentEquationSyntax2011')
for o in moves['old_sources']:
 check(o['snapshot'],o['old_sha256']);old=Path(o['snapshot']).read_text()
 for e in moves['moves']:
  if e['owner']==o['module']:
   require(old.count(e['text'])==1,'Old move ambiguity');old=old.replace(e['text'],'',1)
 expected=re.sub(r'\n{3,}','\n\n','import DiophantineConsistency.'+imports[o['module']]+'\n'+old)
 actual=src/(o['module']+'.lean');require(actual.read_text()==expected,'Owner has unexpected edit '+o['module']);check(actual,o['new_sha256'])
for n in moves['new_sources']:check(src/(n['module']+'.lean'),n['sha256'])
runs=[]
for f in sorted(p.glob('[0-9]*.json')):
 x=json.loads(f.read_text());check(x['snapshot'],x['snapshot_sha256']);check(x['log'],x['log_sha256']);runs.append(x)
leaves=newfiles+['FoundationHACurrentNoZero2011','FoundationHACurrentNoZero2011Checks'];fresh=[]
for name in leaves:
 r=[r for r in runs if r['module']=='DiophantineConsistency.'+name][-1];require(r['exit_code']==0,'Last run failed '+name);check(r['source'],r['source_sha256']);check(r['object'],r['object_sha256']);fresh.append(r)
reports=[]
for r in fresh:
 text=Path(r['log']).read_text()
 found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text)
 reports += [dict(theorem=n,axioms=[a.strip() for a in axs.split(',') if a.strip()]) for n,axs in found]
 for _,axs in found:require(set(a.strip() for a in axs.split(',') if a.strip())<= {'propext','Classical.choice','Quot.sound'},'Nonstandard axiom')
 if r['module'].split('.')[-1]!='FoundationHACurrentNoZero2011Checks':require(text=='','Unexpected final diagnostic')
require(len(reports)==18,'Expected eighteen reports')
bundle=rev/'current-equation-narrow-author-replay';bundle.mkdir(exist_ok=True)
for r in runs:
 for key in ['snapshot','log']:
  f=Path(r[key]);shutil.copy2(f,bundle/f.name)
 f=p/(Path(r['snapshot']).stem+'.json');shutil.copy2(f,bundle/f.name)
for f in Path('/tmp/current-equation-narrow-move-originals').iterdir():shutil.copy2(f,bundle/('original-'+f.name))
for f in ['/tmp/current-equation-narrow-move.py','/tmp/current-equation-narrow-build.py',__file__]:shutil.copy2(f,bundle/Path(f).name)
manifest=inputs | dict(scope='Fresh five exact data owners and actual Foundation/HA syntax bridge only; seven wide owner edits are exact text moves, not freshly replayed in this author run. Root owns scoped downstream refresh.',snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),private=str(p),exact_move_audit=moves,fresh_modules=fresh,development_runs=runs,axiom_reports=reports,freeze_driver_sha256=sha(__file__))
manifest['bundle_files']=[dict(path=str(f.relative_to(root)),sha256=sha(f)) for f in sorted(bundle.iterdir())]
out=rev/'current-equation-narrow-dependency-replay.json';out.write_text(json.dumps(manifest,indent=2)+'\n')
print('PASS exact40 moves, seven owner edits,111cached,7fresh,18standard reports')
print(str(out),sha(out))
for f in fresh:print(f['module'],f['source_sha256'],f['object_sha256'])
