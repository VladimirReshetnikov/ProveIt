#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-vars-final-resume-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-vars-final-resume-check-20261110');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='40af7bbbf8c696b6c2442d5cfac89e41153b04d61216afeb04bc9e8cde07ba6b' and H(A/'outer-result.json')=='eb4e8336e9d4bae88668100f364c9d4f363b4283a0a39781f193b0ad495684b2';o=json.loads((A/'outer-result.json').read_text());assert (o['session_id'],o['exit_code'])==(60596,0) and H(A/'state.json')==H(O/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==5 and len(s['overlay_links'])==1171 and s['runner_sha256']==H(P/'run.py')=='ab64eb7f7197e66d3e5ec33b7c006fe1dbfdbf86e12833487892f6dbc3eafb9d';assert H(P/'source-manifest.json')=='9cbfdab8de614216b88fe7c6d15edcd75f80d86047a6a7a5443f5918c6f5f875';manifest=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroVarsRad1':'d6a64e2179481caeed173f1fe719dc456b06808050687c99a7b61bf44e30aa24'}
names=['Sign33MacroVarsWt0','Sign33MacroVarsWt1','Sign33MacroVarsDm','Sign33MacroVarsKc','Sign33MacroVarsOutput'];theorems=['d41_V0_eq_wt0','d41_V1_eq_wt1','d42_Dm_eq_marg','d43_Kc_eq','recipe_eq_refined'];objs=['cb0d95bd4412a9cb019a301720e85c3f4401063a4b42965ac6d5cecfb204b7cd','4054e3fe10fee0f1a86555ac0f90de842919882587aa7c8342b05058164db585','29c8c3e9c75bf2fd36c44d21a4584a6af2cb84b95521df45ff91a9c59222511f','0086ee95f26670bf3f5cde8c53e1b52edca2b69873a93385bb3f8187ff9397ad','d5cf436d1fe9242862a4b73037e98638bab580377f42dfa60637e6bd0ca2d8d9']
for r,e,n,th,obj in zip(s['rows'],manifest,names,theorems,objs):
 assert r['module']==n and e['module']=='DiophantineConsistency.'+n and H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean')==e['source_sha256']==r['source_sha256'] and H(O/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256']==obj and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'] and v['rss_limit_bytes']==4*1024**3 and v['host_floor_bytes']==10*1024**3 and v['timeout_seconds']==120 and H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  dep=r['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert all(t not in log for t in ('warning:','sorryAx','error:')) and th in log and '[propext, Classical.choice, Quot.sound]' in log;pins[n]=obj
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
up=D/'reviews/nine-seed33-jones-vars-cd-rad-staged-terminal-independent/check.py';assert H(up)=='ca11fb431c4cef5a1a677cd9ebcf2c670dc69a3921e476bed3c8039142603ddd';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
survey=P/'values-survey.py';assert H(survey)=='02cc90fb88600a56e27d8dbc6756571766c6ca7e26a197c621949b09c1216444';x=subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,text=True,timeout=180);assert json.loads(x.stdout)['status']=='PASS'
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':60596,'stages':5,'scope':'nine-input RingVars recipe equals RefinedPair with opaque rank; no full named evaluator or external binding'},indent=2))
