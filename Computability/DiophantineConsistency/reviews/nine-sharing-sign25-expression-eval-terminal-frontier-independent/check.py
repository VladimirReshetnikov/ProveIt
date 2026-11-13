#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-expression-eval-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign25-expression-eval-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='509b12bca5b8565217a8498d9a7489e7ea363da7df87720a0abbf4519fa664bf' and H(A/'outer-result.json')=='773ab308fa8910ec27dc609e449a90121ca4289b792fa9ec213ed8c0d70170df';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(41208,0) and o['state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1060 and s['runner_sha256']==H(P/'run.py')=='7b0b6e0e98340f3e14a77575fceb4e3f568f857d64fa1571fae6c4f79e175f49';names=['Sign25AbstractExpressionDef','Sign25AbstractExpressionEval','Sign25CurrentExpressionDef','Sign25CurrentExpressionEval'];objs=['031970a594f0c816830f356adfb93de4a92452a51c683951bf328ef58be91c23','9ea7ad6be0c1dbc44b957cb50b6b9a55f2203e382544ae33c0979cd138a2520d','759739a7d02784404feef8375cf95ffaf3231f08af5a39172fc52b72e77d12cc','5ad9879f6ceac9321466e21521402c8a6444f2adcaacb98f38eaedfbb0ffe081'];pins={'SharingSeed25Octic':'0f3cba46b15523eca6054d9399ab503e3f11160402ffd228a1fc870a33848f5a','Sign32GenericRemoveInput':'0ab66daaacfbfa8f1d32649124c8eb12ca03e5b7881ca0134041e90152532e3b','CurrentKernelData2011':'95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896',**dict(zip(names,objs))};m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[150,100,150,100][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 if i in (0,2):assert log==''
 else:assert f"'DiophantineConsistency.Sign25{'Abstract' if i==1 else 'Current'}Expression.eval_expression' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign25-expression-eval-prelaunch-frontier-independent/check.py';assert H(pre)=='edaf01ce2293b995f6419ce273ede4b758ccd9a5b21eab95487ee7e1be7847c9'
for f,h in [('partial-survey.py','14bf2ba8ea32195854fa2307eef0c485db28f7c28e519cfe0e782e3641cbde2b'),('seed-data-survey.py','10ab328c0954fa189ba916747285f1b63cfa37dd08cce4df3f1fb9890a639d3b')]:
 p=P/f;assert H(p)==h;r=subprocess.run([sys.executable,'-I','-S','-B',str(p)],check=True,capture_output=True,text=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS'
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':41208,'stages':4,'guards':500,'links':1060,'scope':'input-zero fixed to 1, abstract/current-port expression evaluations only; partial producer ancestry retained'},sort_keys=True,indent=2))
