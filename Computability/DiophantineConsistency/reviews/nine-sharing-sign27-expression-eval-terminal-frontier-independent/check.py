#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-expression-eval-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign27-expression-eval-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='6235877cddc54ead825a7b74c45e5ecf8715d1c53e668e440a70f1bf77acddf4' and H(A/'outer-result.json')=='1faf2698ab6c821e0893cb37151efb2757e394958494dc82e226655d31465f32';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(24294,0) and o['retained_state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1060 and s['runner_sha256']==H(P/'run.py')=='6d4d52b69453c8ed0aad647ef47049a9995df3b5a50503988f758eb8c4209200';names=['Sign27AbstractExpressionDef','Sign27AbstractExpressionEval','Sign27CurrentExpressionDef','Sign27CurrentExpressionEval'];objs=['03ac6535716e0f4ef70acae9898d428d24bc199fe0379128d20fc50d576ce6e2','9ec6ea228a097f0ab1fb55bc34df425d6166e6042f14145ce1e46264335899b5','697f18e47243f7bba0f0bbc5b17b0addd10b447f651abef82f0af4ab23ee6fe7','a91b5913206a8111c9b1d6710806af7eb4985c2d7c0b63dac0fd1848e9a50d6f'];pins={'SharingSeed27Sextic':'8313b5570e835ea52d66d7c33c64514d511173efcb1dab0166e701af3798e356','Sign32GenericRemoveInput':'0ab66daaacfbfa8f1d32649124c8eb12ca03e5b7881ca0134041e90152532e3b','CurrentKernelData2011':'95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896',**dict(zip(names,objs))};m=json.loads((P/'source-manifest.json').read_text())['rows']
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
 else:assert f"'DiophantineConsistency.Sign27{'Abstract' if i==1 else 'Current'}Expression.eval_expression' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign27-expression-eval-prelaunch-frontier-independent/check.py';assert H(pre)=='d140be6cc80ff0c5ed4a88db07276529db2497dfedafd9c3ea4c7e0e0687c322'
for f,h in [('partial-survey.py','627f360ae739f6e1bac7bf14d89687e963f299c81b81a7eb7492b2e09a0cb637'),('seed-data-survey.py','40b06640255498a93f8a403f13108e6e09311ef6f5ab785b02205ea23a452d39')]:
 p=P/f;assert H(p)==h;r=subprocess.run([sys.executable,'-I','-S','-B',str(p)],check=True,capture_output=True,text=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS'
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':24294,'stages':4,'guards':500,'links':1060,'scope':'input-zero fixed to 1, abstract/current-port expression evaluations only; partial producer ancestry retained'},sort_keys=True,indent=2))
