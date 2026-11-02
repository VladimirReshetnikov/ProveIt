#!/usr/bin/env python3
import hashlib,importlib.util,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge/compact44-controller-pair-prototype';OUT=Path('/tmp/ipra-compact-controller-pair-01');PARENT=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');VIEW=Path('/tmp/ipra-historical-audit-review-01');EP=BASE/'reviews/thirteen-model-endpoint-successor-pair-independent-audit';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name in ['PAIR_RESULT.md','evidence/receipt.json','evidence/terminal-observation.json','evidence/author/ArithmeticControllerDataCompact44.log','evidence/author/ArithmeticControllerChoiceCompact44.log','evidence/peer/ArithmeticControllerDataCompact44.log','evidence/peer/ArithmeticControllerChoiceCompact44.log']:
 p=PKG/name;rel=p.relative_to(ROOT).as_posix();blob=subprocess.run(['git','show','692b5249e6:'+rel],cwd=ROOT,check=True,capture_output=True).stdout;assert hashlib.sha256(blob).hexdigest()==H(p),name
R='171e89710e85da860e135ea5f96694dfb836ce4dfe5c7a6559d3a79c2939a496';assert H(PKG/'evidence/receipt.json')==H(OUT/'receipt.json')==R
term=json.loads((PKG/'evidence/terminal-observation.json').read_bytes());assert term['session_id']==53204 and term['observed_exit']==0 and term['receipt_sha256']==R and term['protected_head']=='cd7e4e722ef805a263fc9c28a8547542ae56bdc2' and term['compiler_children']==4
rec=json.loads((OUT/'receipt.json').read_bytes());assert len(rec['runs'])==2;assert rec['status']=='PASS_PAIRED_COMPACT_CONTROLLER' and rec['head']==term['protected_head'] and rec['driver_sha256']==H(PKG/'replay.py')=='bea24a34e875a7b3b8a6de47b1982609449d528aeed8cca9ddfda5961a28b753'
assert H(BASE/'reviews/compact44-controller-pair-prelaunch-independent-audit/CHECK.json')=='4dc027c715e832b7a6cb1474bdb737dea64a327b39688bcd875f64e98525d3f5'
for name,x in rec['direct_and_output_guards'].items():
 p=Path(name)
 if x is None:assert not os.path.lexists(p),name
 else:assert p.is_file() and str(p.resolve())==x['realpath'] and H(p)==x['sha256'],name
assert len(rec['direct_and_output_guards'])==140
sp=importlib.util.spec_from_file_location('controller_driver',PKG/'replay.py');d=importlib.util.module_from_spec(sp);sp.loader.exec_module(d)
expected_logs=[d.observed_expected(x) for x in d.OBS]; expected_reports=[['g_mod_nat','zc_surj','zc_inj'],['controller_choice','rank_calibration']];suffixes=d.SUFFIXES;guardkeys=set();results=[]
for run,side in zip(rec['runs'],('author','peer')):
 assert run['side']==side and len(run['steps'])==2
 lib=OUT/side/'lib';base=PARENT/side/'lib';original={p.relative_to(base) for p in base.rglob('*.olean')};actual={p.relative_to(lib) for p in lib.rglob('*.olean')};extra={Path('DiophantineConsistency/ArithmeticControllerDataCompact44.olean'),Path('DiophantineConsistency/ArithmeticControllerChoiceCompact44.olean')};assert not original & extra and actual==original|extra
 for rel in original:assert (lib/rel).resolve()==(base/rel).resolve() and H(lib/rel)==H(base/rel),str(rel)
 steps=[]
 for i,(row,source) in enumerate(zip(run['steps'],(d.DATA,d.CHOICE))):
  name=source.stem;src=OUT/'src/DiophantineConsistency'/source.name;obj=lib/'DiophantineConsistency'/(name+'.olean');log=OUT/side/(name+'.log');copy=PKG/'evidence'/side/(name+'.log')
  assert row['module']==name and row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None
  assert src.is_file() and not src.is_symlink() and H(src)==H(source)==row['source_sha256']==d.PINS[source]
  assert obj.is_file() and not obj.is_symlink() and H(obj)==row['object_sha256'];assert H(log)==H(copy)==row['log_sha256']
  text=log.read_text();assert text==row['stdout'] and text.replace(str(src),'<SOURCE>')==expected_logs[i] and 'sorryAx' not in text and 'error:' not in text
  reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.M);prefix='DiophantineConsistency.'+name+'.';assert [n for n,_ in reports]==[prefix+n for n in expected_reports[i]] and all({a.strip() for a in v.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,v in reports)
  assert text.count('warning:')==[1,2][i]
  init=PACKAGE/'Init.olean';deps=[init,lib/'DiophantineConsistency/ArithmeticStandardCasts.olean',lib/'DiophantineConsistency/ArithmeticControllerLift.olean',lib/'DiophantineConsistency/ArithmeticPackingBlocks.olean',PACKAGE/'Mathlib/Tactic/ReduceModChar.olean'] if i==0 else [init,lib/'DiophantineConsistency/ArithmeticControllerDataCompact44.olean',lib/'BusyBeaver/ZFC/ArithmeticCantor.olean']
  assert all(x.is_file() for x in deps) and set(row['deps_stdout'].splitlines())==set(map(str,deps))
  for item in deps+[obj]:
   for suffix in suffixes:guardkeys.add(str(item)[:-6]+suffix)
  assert set(row['direct_guards'])=={str(z)[:-6]+suffix for z in deps for suffix in suffixes}
  steps.append({'module':name,'compiler_exit':row['compiler_exit'],'deps_exit':row['deps_exit'],'warnings':text.count('warning:'),'named_reports':len(reports),'object_sha256':H(obj)})
 results.append({'side':side,'inherited_olean_count':len(original),'steps':steps})
assert set(rec['direct_and_output_guards'])==guardkeys
assert [x['object_sha256'] for x in results[0]['steps']]==[x['object_sha256'] for x in results[1]['steps']]
q=subprocess.run([sys.executable,'-I','-S','-B',str(BASE/'reviews/historical-endpoint-contextual-audit/contextual-endpoint.py'),'--historical-view',str(VIEW)],cwd=ROOT,capture_output=True,timeout=1200)
assert q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((EP/'CHECK.json').read_bytes())
print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT_CONTROLLER_PAIR_AUDIT','evidence_commit':'692b5249e6','receipt_sha256':R,'recorded_outer_session':53204,'recorded_outer_exit':0,'recorded_protected_head':term['protected_head'],'contextual_parent_rerun_exit':q.returncode,'direct_and_output_companion_guards':len(guardkeys),'runs':results,'scope':'Conditional model controller over contextual historical endpoint; no unchanged live parent pass, current-source validation, retained graph/K binding, machine or iPRA theorem; provider and axiom-inventory limits inherited.'},indent=2))
