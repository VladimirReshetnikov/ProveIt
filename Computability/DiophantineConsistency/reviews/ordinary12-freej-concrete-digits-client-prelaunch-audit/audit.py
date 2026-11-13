#!/usr/bin/env python3
"""Static/no-Lean review of exact conditional concrete-digit join replay."""
import hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
ROOT=Path.cwd();BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge/free-j-concrete-digits-client-prototype';DRIVER=PKG/'replay.py'
H='9b760773ff4a03a67226406868ecc3de17902154c9515da20e502024f408a6bf'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 name=DRIVER.relative_to(ROOT).as_posix();blob=subprocess.run(['git','show','43f3310a79:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
 need(hashlib.sha256(blob).hexdigest()==sha(DRIVER)==H,'driver bytes')
 s=importlib.util.spec_from_file_location('reviewed_digits',DRIVER);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
 for p,h in m.PINS.items():need(sha(p)==h,'fixed pin '+str(p))
 scan=json.loads((m.PLAN/'scan.json').read_bytes());parent=json.loads((m.AUDIT/'CHECK.json').read_bytes());plan=json.loads(m.PLAN_AUDIT.read_bytes())
 need(scan['status']=='PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD' and len(scan['modules'])==12 and len(scan['inherited_objects'])==114,'plan')
 need(parent['status']=='PASS_INDEPENDENT_FREEJ_SATURATION_CLIENT_AUDIT' and parent['recorded_outer_exit']==0 and plan['status']=='PASS_INDEPENDENT_FREEJ_CONCRETE_DIGITS_SOURCE_CLOSURE_AUDIT','audited parents')
 for row in scan['modules']:
  p=Path(row['source']);need(sha(p)==row['source_sha256'],'module source '+row['module'])
  imports=[x for l in p.read_text().splitlines() if l.startswith('import ') for x in l[7:].split()];need(imports==row['imports'],'module imports '+row['module'])
 for choice in scan['explicit_choices'].values():
  need(sha(choice['selected'])==choice['selected_sha256'],'selected source')
  for c in choice['all_candidates']:need(sha(c['path'])==c['sha256'],'candidate')
 for side in ('author','peer'):
  lib=m.PREFIX/side/'lib';objs={str(p.relative_to(lib)):p for p in lib.rglob('*.olean')};need(len(objs)==114 and set(objs)=={x['module_path'] for x in scan['inherited_objects']},'provider inventory')
  for row in scan['inherited_objects']:
   p=objs[row['module_path']];need(sha(p)==row['sha256'] and str(p.resolve())==row[side+'_resolved_path'],'provider hash '+row['module_path'])
 results=[]
 for script in (str(Path(__file__).resolve().parent/'mock_loop.py'),str(Path(__file__).resolve().parent/'guards.py')):
  q=subprocess.run([sys.executable,'-I','-S','-B',script],cwd=ROOT,capture_output=True,text=True,timeout=120)
  need(q.returncode==0 and not q.stderr,'control '+script+' '+q.stderr);results.append({'script':Path(script).name,'exit':q.returncode,'stdout':q.stdout})
 need('good PASS fake_children 26' in results[0]['stdout'],'26 fake steps')
 need(sha(DRIVER)==H,'post driver hash')
 print(json.dumps({'status':'PASS_CONDITIONAL_FREEJ_CONCRETE_DIGITS_PRELAUNCH_AUDIT','driver_commit':'43f3310a79','driver_sha256':H,'source_count':12,'inherited_objects_per_side':114,'controls':results,'scope':'No Lean build. Separately observed full parent preflight recorded in terminal observation. Symbolic graph-low-port equality and other premises remain explicit; no retained-MC, checker or PRA proof. Requires trusted initial loader and external stable-HEAD/sole-Lean window; point-in-time and inherited resource/provider limitations.'},indent=2))
if __name__=='__main__':main()
