#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-rank-symbolic-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-prefix-rank-symbolic-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='509bf124ad9ec3029f0246602a05b62bd35b4039047533f460a43650e95b2445' and H(A/'outer-terminal-author-record.json')=='3b8ba7cf05d4f93c3dc0ec2a68135b1200badb0c5f84f9b785f79b14345d2858';s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal-author-record.json').read_text());assert s['status']=='PASS' and (o['session_id'],o['exit_code'])==(52765,0) and len(s['rows'])==3 and len(s['overlay_links'])==1079 and s['runner_sha256']==H(P/'run.py')=='30c3aa07efc46971a8940fb8efc1931f2a4ef6c9312f0435f2a590eb0665995d'
names=['Sign33MacroRankValuesSums','Sign33MacroRankValuesOther','Sign33MacroRankSymbolic'];objs=['662da44e79840d6bb17b9920fc92998e619e723c6155901b38ee04ee7d8983d3','398e12fc6831b4063822ce8a8b16b5ba2fa29d8c841c015aac328f8caf2988ea','b03354a0d7e2d662f5da26cd1a08adf15808912145b1d3a39f0c907518979a6f'];deps=[{'Sign33MacroPrefixE':'a56f7d3448740f9a1b926ba82c9da13a58c29ab54cd8175d1464978298f3959a','Sign33MacroPrefixEll':'0ae3b42fce126754676f45a851c98f2aff6a679056db9a51e503ab60c2424026','Sign33MacroPrefixLambda':'ebf67b62c3686e73995a0708230f464de83eb11fc10d02b17bff34f642790666','Sign33MacroRankComposition':'848263c5c75e6c09c16a345ee38fa48adc8ab5883ccffd2184631ae39bb49c1d'},{'Sign33MacroPrefixGsmall':'c5f5b65538743b2bd08f5e7e5dd1cc8fd95bef8e48a46801c303c53598ed230d','Sign33MacroPrefixTheta':'4897155b8bca501868fab555b6b1344ca955c985b4e007b4dc200d4ed2aca1d3','Sign33MacroRankValuesSums':objs[0]},{'Sign33MacroRankValuesOther':objs[1]}];ths=[['Sign33MacroRankValues.d10_e_value','Sign33MacroRankValues.d10_ell_value','Sign33MacroRankValues.d10_lambda_value'],['Sign33MacroRankValues.d10_b_value','Sign33MacroRankValues.d10_g_value','Sign33MacroRankValues.d10_theta_value'],['Sign33MacroRankSymbolic.d11_rank_symbolic']];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[250,200,100][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'] and H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod,h in deps[i].items():
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-prefix-rank-symbolic-prelaunch-frontier-independent/check.py';assert H(review)=='41c2989a873b865dae03418b3c24bdcc3efdfcacb558d90b7713aa1d856a6f94'
survey=P/'values-survey.py';assert H(survey)=='4a0b1384aef69c99413ac545406e3a99463467147274b0eb2dc15ccf3cb77206';subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,timeout=60)
review=D/'reviews/nine-seed33-jones-prefix-rank-composition-terminal-frontier-independent/check.py';assert H(review)=='1c4186904c2c24b91650e9824a11b167656686e65459979e8c626abcb63ceff8';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=60)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':52765,'stages':3,'guard_slots':550,'overlay_links':1079,'scope':'symbolic d11 short-prefix rank only'},sort_keys=True,indent=2))
