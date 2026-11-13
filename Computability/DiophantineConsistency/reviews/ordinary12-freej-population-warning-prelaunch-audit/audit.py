#!/usr/bin/env python3
"""No-Lean exact warning correction review with preserved first failure."""
import hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/free-j-population-client-prototype';HERE=Path(__file__).resolve().parent
OLD=BASE/'reviews/ordinary12-freej-population-client-prelaunch-audit';FAILED=PKG/'observations/failed-pair-01';OUT=Path('/tmp/ipra-freej-population-client-pair-01');DRIVER=PKG/'replay.py'
NEW='ab21a262ef9ba39ba3c6dc57e1899bc8f2574231e2f1222171b547c37699d725'; PREVIOUS='793a6873afd3517b85828e54421ee16cbd6077091b08318fb6bc62611d20de8f'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 name=DRIVER.relative_to(ROOT).as_posix();original=subprocess.run(['git','show','189b41c279:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
 need(hashlib.sha256(original).hexdigest()==sha(DRIVER)==NEW and sha(FAILED/'replay.py')==PREVIOUS,'driver pins')
 need(sha(OLD/'CHECK.json')=='c8375551696986a06bc5d030a5168b7a5a9eae6efd440102f49288cdaad58b02','old review')
 old=json.loads((OLD/'CHECK.json').read_bytes());need(old['driver_sha256']==PREVIOUS and old['status']=='PASS_CONDITIONAL_FREEJ_POPULATION_CLIENT_PRELAUNCH_AUDIT','old review status')
 term=(FAILED/'terminal.txt').read_text();need('session 52770 actually exited 1' in term and 'No peer modules ran and no paired receipt was produced' in term,'failure observation')
 names=['ArithmeticPow','ArithmeticHalfBinomialSandwich','ArithmeticBinomPascal','ArithmeticBinomExpansion','ArithmeticBinomFactorial','ArithmeticBinaryPopulation','ArithmeticBinomLegendre']
 scan=json.loads((BASE/'research/ordinary12-ipra-bridge/free-j-population-closure-plan/scan.json').read_bytes());expected={x['module'].split('.')[-1]:x['source_sha256'] for x in scan['preferred_rebuild']}
 for i,n in enumerate(names):
  file='DiophantineConsistency_'+n+'.log';need(sha(FAILED/file)==sha(OUT/'author'/file),'failure log '+n)
  src=OUT/'frozen/DiophantineConsistency'/(n+'.lean');obj=OUT/'author/lib/DiophantineConsistency'/(n+'.olean')
  need(sha(src)==expected[n] and obj.is_file(),'failed-run frozen source/object '+n)
  if i<6:need((FAILED/file).read_bytes()==b'','unexpected earlier log '+n)
 need(not (OUT/'peer').exists() and not (OUT/'receipt.json').exists(),'failed run accepted')
 spec=importlib.util.spec_from_file_location('warning_driver',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 warning=(FAILED/'DiophantineConsistency_ArithmeticBinomLegendre.log').read_text();src=OUT/'frozen/DiophantineConsistency/ArithmeticBinomLegendre.lean'
 need(m.warnings_accepted('DiophantineConsistency.ArithmeticBinomLegendre',src,warning),'exact observed warning')
 for text in (warning.replace(':78:10:',':78:11:'),warning+'extra warning: altered\n','',warning.replace('simpa','simp')):
  need(not m.warnings_accepted('DiophantineConsistency.ArithmeticBinomLegendre',src,text),'unexpected accepted warning')
 need(not m.warnings_accepted('DiophantineConsistency.ArithmeticPow',src,warning) and m.warnings_accepted('DiophantineConsistency.ArithmeticPow',src,''),'wrong-module control')
 scan,parent=m.verify();need(len(scan['preferred_rebuild'])==9 and len(scan['freej_base_objects'])==97 and parent['status']=='PASS_INDEPENDENT_FREEJ_POWER_FINISH_AUDIT','real preflight')
 controls=[]
 for script,args in [(HERE/'mock_loop.py',[]),(PKG/'warning_controls.py',[]),(PKG/'warning_controls.py',['-O'])]:
  r=subprocess.run([sys.executable,*args,'-I','-S','-B',str(script)],capture_output=True,text=True,timeout=60)
  if args:need(r.returncode!=0 and 'optimized Python rejected' in r.stderr,'optimized rejection')
  else:need(r.returncode==0 and not r.stderr,'control '+str(script))
  controls.append({'script':script.name,'args':args,'exit':r.returncode,'stdout':r.stdout})
 need(sha(DRIVER)==NEW,'post driver drift')
 print(json.dumps({'status':'PASS_CONDITIONAL_FREEJ_POPULATION_WARNING_PRELAUNCH_AUDIT','driver_commit':'189b41c279','driver_sha256':NEW,'prior_driver_sha256':PREVIOUS,'recorded_failed_outer_session':52770,'recorded_failed_outer_exit':1,'failed_author_logs_checked':len(names),'read_only_preflight':'PASS','controls':controls,'scope':'No Lean compile. Accepts only exact observed one-module linter warning; trusted clean initial loader and externally enforced stable-HEAD/sole-Lean window required; point-in-time provider/source checks and inherited sampled-resource/package-transitive/dynamic boundaries.'},indent=2))
if __name__=='__main__':main()
