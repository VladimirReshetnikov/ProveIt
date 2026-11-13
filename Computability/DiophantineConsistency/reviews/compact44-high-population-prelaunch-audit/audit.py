#!/usr/bin/env python3
"""No-Lean static, independent external and fake-loop high-mask review."""
import hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge/compact44-high-population-prototype';HERE=Path(__file__).resolve().parent
DRIVER=PKG/'replay.py';EXPECTED='52b10e75fe24d6aa883b7db3c011171ce7c5fc82e5c45e46ba0a39aa4aa1fd30'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 prefix=PKG.relative_to(ROOT).as_posix()+'/'
 names=subprocess.run(['git','ls-tree','-r','--name-only','eb3e089ecb','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines();need(len(names)==19,'packet inventory')
 for n in names:
  blob=subprocess.run(['git','show','eb3e089ecb:'+n],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(blob).hexdigest()==sha(ROOT/n),'packet bytes '+n)
 need(sha(DRIVER)==EXPECTED,'driver hash')
 spec=importlib.util.spec_from_file_location('high_review',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.check_pins()
 log=(PKG/'observations/attempt03.log').read_text();need(log=="'CompactHighPopulation.model_population' depends on axioms: [propext, Classical.choice, Quot.sound]\n'CompactHighPopulation.model_lt' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'single-side successful reports')
 for i in (4,6,7,8):
  x=(PKG/f'observations/attempt{i:02}.log').read_text();need('maximum recursion depth' in x and 'sorryAx' in x,'failed mod-8 recursion '+str(i))
 need('memory_exception' in (PKG/'observations/attempt05.log').read_text(),'failed mod-8 memory')
 checks=[]
 for script,args in [(HERE/'check_external.py',[]),(HERE/'check_external.py',['-O']),(PKG/'check_display.py',[]),(PKG/'check_display.py',['-O']),(HERE/'mock_loop.py',[]),(HERE/'guards.py',[])]:
  q=subprocess.run([sys.executable,*args,'-I','-S','-B',str(script)],capture_output=True,text=True,timeout=120)
  need(q.returncode==0 and not q.stderr,'control '+str(script)+' '+q.stderr);checks.append({'script':script.name,'args':args,'exit':q.returncode,'stdout':q.stdout})
  if script.name in ('check_external.py','check_display.py'):
   d=json.loads(q.stdout);need(d['length']==8807 and d['digits_checked']==8807 and d['population']==986,'external count')
 need('good PASS fake_children 2' in checks[-2]['stdout'],'fake loop')
 need(sha(DRIVER)==EXPECTED,'post driver pin')
 print(json.dumps({'status':'PASS_CONDITIONAL_COMPACT44_HIGH_POPULATION_PRELAUNCH_AUDIT','source_commit':'eb3e089ecb','driver_sha256':EXPECTED,'external_digit_count':8807,'external_population':986,'reported_successful_exploration_session':70407,'failed_optional_mod8_attempts':[4,5,6,7,8],'controls':checks,'scope':'No Lean build. Independent finite source/recipe/bytes check; no internal retained-MF/graph-port identity, mod-8 theorem, machine or iPRA. Separately observed full parent preflight recorded in terminal observation; trusted initial loader and external stable-HEAD/sole-Lean window required.'},indent=2))
if __name__=='__main__':main()
