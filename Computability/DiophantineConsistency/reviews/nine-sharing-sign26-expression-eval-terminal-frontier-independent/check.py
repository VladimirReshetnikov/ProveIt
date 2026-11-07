#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-expression-eval-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-expression-eval-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='2deb0d1a6bf67cd0829ba1f16a2bea1f02bb9637bf2625ca3c4ce926fc3c6378' and H(A/'outer-result.json')=='84199558f4a67594155e865f654c638de6e59e29b10fa93759c07426c1408da0';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(22155,0) and o['state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1060 and s['runner_sha256']==H(P/'run.py')=='63563085b2ac9747057561b4ef780bd8d90ee75a61e8474a0df919906e8e88b8';names=['Sign26AbstractExpressionDef','Sign26AbstractExpressionEval','Sign26CurrentExpressionDef','Sign26CurrentExpressionEval'];objs=['399e536a32c2dfeaa87a11ce56fa14a82eca0002afe9ec968bbbbe63c3dee528','2d0fd542a168944986d58a3b5952a67976f8221db8802ef4b0e4e89ba6436ff3','8302c0ff4fb24cffc32d18fd5429d86c90f2934e7046bbde8d52677c75e76403','93eb07957c23cc42b56a0fd5b513495c04e8d6e8beba3da6c8e5b2c8a2232e9e'];pins={'SharingSeed26Sextic':'49d762d74de47777373cf5bc09122915cfbf25e29e0adbcf020d5e6ece8e713d','Sign32GenericRemoveInput':'0ab66daaacfbfa8f1d32649124c8eb12ca03e5b7881ca0134041e90152532e3b','CurrentKernelData2011':'95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896',**dict(zip(names,objs))};m=json.loads((P/'source-manifest.json').read_text())['rows']
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
 else:assert f"'DiophantineConsistency.Sign26{'Abstract' if i==1 else 'Current'}Expression.eval_expression' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-expression-eval-prelaunch-frontier-independent/check.py';assert H(pre)=='a82d074e3b36fe1ffa5a60b6e2240ac01f958f1889f8238797f1d994a2ca8ed5'
for f,h in [('partial-survey.py','44c34680847c45ce846cbd1853cb819a3e2794ce64c91f810b7dc24a07455ba0'),('seed-data-survey.py','d090d2f4a088f89f4c8f091bc6c9267ef4af28402a675c91631435287e1e809e')]:
 p=P/f;assert H(p)==h;r=subprocess.run([sys.executable,'-I','-S','-B',str(p)],check=True,capture_output=True,text=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS'
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':22155,'stages':4,'guards':500,'links':1060,'scope':'input-zero fixed to 1, abstract/current-port expression evaluations only; partial producer ancestry retained'},sort_keys=True,indent=2))
