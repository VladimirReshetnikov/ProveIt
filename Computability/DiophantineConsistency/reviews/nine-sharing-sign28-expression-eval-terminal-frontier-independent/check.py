#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-expression-eval-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-expression-eval-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='dc24e097ce96bd560aa0320e237ce1c67155ff4af9b5210e5f8a873d23677a0c' and H(A/'outer-result.json')=='0b31be590d73072c0b5a48ee676e69909f2cf05bf59ca80b21e0e831fd7a5f61';s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='PASS' and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(17743,0) and o['retained_state_sha256']==H(A/'state.json') and len(s['rows'])==4 and len(s['overlay_links'])==1074 and s['runner_sha256']==H(P/'run.py')=='618102d947c02971999ed8f0db3f7f551bdffa425c1e1d6a1052403638363196'
names=['Sign28AbstractExpressionDef','Sign28AbstractExpressionEval','Sign28CurrentExpressionDef','Sign28CurrentExpressionEval'];objs=['70ec7a87bed50e9c96d0fa34d537705d2d37800f1435dd35b208d2aa08f99917','8fefa86d9c407e9e64f7271299a93af2e7ea867efe7e3714acf46651aa9d73ad','b8f6f5c54db50380b9ddee64a3ba62cda55bb2aae2af8fef2bbda22eebd6da59','2992d47b5eb75108840295f5461f5e804359bc602c7cde75908e5f2189cdc68f'];deps=[{'SharingSeed28Sextic':'cbe6fe0a7b11251074e6795a020693513cec8f64b92bfcd58da2583c1b99ab4f','Sign32GenericRemoveInput':'0ab66daaacfbfa8f1d32649124c8eb12ca03e5b7881ca0134041e90152532e3b'},{names[0]:objs[0]},{'CurrentKernelData2011':'95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896',names[1]:objs[1]},{names[2]:objs[2]}];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[150,100,150,100][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'] and H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod,h in deps[i].items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 if i in (1,3):
  name=['Sign28AbstractExpression','Sign28CurrentExpression'][(i-1)//2];assert f"'DiophantineConsistency.{name}.eval_expression' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
 else:assert not log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-expression-eval-prelaunch-frontier-independent/check.py';assert H(review)=='ed4b00a39c907e9aadc62630986ba300943d7c0d3435267708da4f5993b4e31f'
for n,h in [('partial-survey.py','368cf208a43b0a798b93f32bd839036f8407c8b9fc1543718ae9fa173ab20965'),('seed-data-survey.py','7b9414ac436104231920b38fb25b4b712d2bf6ab7c92c2a725101016daf726ec')]:
 f=P/n;assert H(f)==h;subprocess.run([sys.executable,'-I','-S','-B',str(f)],check=True,capture_output=True,timeout=60)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':17743,'stages':4,'guard_slots':500,'overlay_links':1074,'scope':'abstract and current input-removal definitions/evaluations only'},sort_keys=True,indent=2))
