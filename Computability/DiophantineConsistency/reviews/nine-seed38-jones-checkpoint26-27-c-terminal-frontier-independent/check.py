#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint26-27-c-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint26-27-c-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')=='26b4857f2ec7d7d4b7dd0c3cb27f493b9f5dab0bf11510b47bdaae91e8ab8a5d' and sha(a/'outer-terminal-author-record.json')=='335c152c5c34fa364943292144b5f028029e042043ad40f420cd5af7b2440089';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(17426,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1240
names=['Norm38MacroCInputs','Norm38MacroCBW','Norm38MacroCValue'];objects=['a2c0867377a0f32c16e02893a8eb5be448a263cad0f2a2609481d370002bbb72','74bd899ef6a38de10b3e4188d00e873cc65d2d9d16596bf24390abfdfa031856','460ceb6124d38eedff80b049022612adcd2e4f8a5fbd76dd6e44fcfa532ea764'];reports=[['d18_b_value','d18_phi_value'],['d26_Bprime_value','d26_W_value'],['d27_C_value']];guards=[300,250,150]
expected=[{'Norm38MacroJPath':'d4a2147466024442645d58e1cd9a6f0943b8ecdcf30ab6b1a5a08eb620cf3ca6','Norm38MacroLive18Group01':'b2c531a9eecdd13baaf18f2f130949cd8fd7602118f575cd124fffa4b0dc32dd','Norm38MacroLive18Group03':'2589ac6c78d736a31bd3e851aaa0068d43ec0a10a10b3cb648b4df8b7da9d902','Norm38MacroPrefixInputsB':'43b71a21b7efa4d263709791c323ac49005a3e3b28542836890e094710474170','Norm38MacroPrefixGlarge':'b685399878adfa8efc0fae22b6f9793c1f74079b4266cfff15d86a6a25e89a06'},{'Norm38MacroCInputs':objects[0],'Norm38MacroDependentW':'3f9a9d120dfc07e6dc0ce22145f5a9d76309838bbd7f6ae1f17f7b6efbb2b18d','Norm38MacroLive18Group02':'f028ef640af09a6477b7672e76630057147c859c26d908dafded919953f8a53c','Norm38MacroUYInputs':'26bf3e4788614e5d5efe6d131734539f551d9d8cbc50fb65b8b017d3b2ff828e'},{'Norm38MacroCBW':objects[1],'Norm38MacroDependentC':'8a69d181c2584313ff4add42d2197020e387b888cd676fbfa4dc465a305bd281'}]
for r,n,h,ts,gn,ex in zip(s['rows'],names,objects,reports,guards,expected):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and len(r['direct_guard'])==gn
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpointC\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for mod,digest in ex.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS','author_recorded_outer_session':17426,'stages':3,'guard_slots':700,'overlay_links':1240,'scope':'symbolic C at d27 with opaque rank; no Lean replay'},indent=2,sort_keys=True))
