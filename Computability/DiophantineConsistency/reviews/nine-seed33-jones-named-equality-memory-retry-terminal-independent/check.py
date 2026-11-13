#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-seed33-jones-named-equality-memory-retry-check';a=p/'attempt01';out=Path('/tmp/nine-seed33-jones-named-equality-memory-retry-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='5ed91c44504927c094b7254bd399358b5e183e020db47864626706c60f749d8e' and sha(a/'outer-result.json')=='f69decc7244c8aede2b4ec95a0a0a3b7b4c30da12b43eab1eb54707e589e7322';o=json.loads((a/'outer-result.json').read_text());assert (o['session_id'],o['exit_code'])==(37533,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and len(s['rows'])==2 and len(s['overlay_links'])==1388 and s['runner_sha256']==sha(p/'run.py')=='742c4e8bb3da0a4bdc94b4d555d38056c4d0ecaa93e10ec9c4a81b9659ada87c';entries=json.loads((p/'source-manifest.json').read_text())['rows'];names=['Sign33MacroNamedVars','Sign33MacroNamedEquality'];objs=['ea81b8a5856c5b2457529c5760e8b979aa6b826c69b9b73ace0d8c2665ac5b3f','74f3d19863bd29d113c3111fe0f14f6ea2040edaa18264d29a4debf16b41d5fb'];pins={'Sign33MacroVarsOutput':'d5cf436d1fe9242862a4b73037e98638bab580377f42dfa60637e6bd0ca2d8d9','Sign33NamedFormula':'ba39e705f4cc32ec52ddf0fc992d1500139f46b270bbe36cba07bddcbac1435f'};warnings=0
for r,e,n,obj,th in zip(s['rows'],entries,names,objs,['vars_eq_named','recipe_eq_expression_eval']):
 assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']==obj
 for ph in ('deps','compile'):
  v=r[ph];log=n+'-'+ph+'.txt';assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'] and v['rss_limit_bytes']==4*1024**3 and v['host_floor_bytes']==10*1024**3 and v['timeout_seconds']==120 and sha(a/log)==sha(out/log)==v['log_sha256']
 for mod in e['imports']:
  dep=r['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 log=' '.join((a/(n+'-compile.txt')).read_text().split());assert 'error:' not in log and 'sorryAx' not in log and th in log and '[propext, Classical.choice, Quot.sound]' in log;warnings+=log.count('warning:');pins[n]=obj
assert warnings==1
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
survey=p/'provider-survey.py';assert sha(survey)=='c89fe6d6d02beb285362261a1c25b2f49e453794e9c4b530b9d0db560c53ac9d';x=subprocess.run([sys.executable,'-I','-S','-B',str(survey)],capture_output=True,text=True,timeout=360);assert x.returncode==0 and not x.stderr;d=json.loads(x.stdout);assert d['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY' and len(d['union'])==1388
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':37533,'stages':2,'warnings':warnings,'scope':'Fin9 commutative-ring macro recipe equals symbolic named expression evaluator; external binding separate'},indent=2))
