#!/usr/bin/env python3
"""Freeze the 42-variable native endpoint on the matched native-33 provider."""
import hashlib,json,os,re,sys
from pathlib import Path
R=Path.cwd().resolve();V=R/'Computability/DiophantineConsistency/reviews';SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
D=Path(__file__).resolve().parent; O=Path(sys.argv[1]).absolute(); assert not O.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
N=V/'ipra-named33-native-replay-input';VR=V/'ipra-named33-native-verification';TR=V/'ipra-named33-native-terminal-observations';MR=V/'adaptive-square-sums42-model-replay'
parent=Path('/tmp/ipra-named33-native-zqgw2b3i');m22=json.loads((N/'manifest.json').read_text());pm=m22['inherited_manifest'];state=json.loads((parent/'state.json').read_text());rec=json.loads((VR/'receipt.json').read_text());mt=json.loads((MR/'receipt.json').read_text())
assert state['status']=='PASS' and state['manifest_sha256']==H(N/'manifest.json') and rec['peer_path']==str(parent) and rec['peer_state_sha256']==H(parent/'state.json') and rec['rows']==4 and rec['status']=='MATCHED_PASS'
term=json.loads((VR/'terminal-observation.json').read_text());assert term['observed_exit_code']==0 and term['receipt_sha256']==H(VR/'receipt.json')
modelterm=json.loads((MR/'session-observation.json').read_text());assert modelterm['observed_exit_code']==0 and modelterm['receipt_sha256']==H(MR/'receipt.json')
assert mt['status']=='MATCHED_PASS' and len(mt['runs'])==2 and mt['runs'][0]['rows']==mt['runs'][1]['rows']
assert all(x['exit']==0 for run in mt['runs'] for x in run['rows'])
gate={}
def pin(p):
 p=Path(p).absolute();assert p.is_file() and p.resolve()==p;gate[str(p)]=H(p)
for p in [N/'manifest.json',N/'prepare.py',N/'replay.py',VR/'receipt.json',VR/'terminal-observation.json',VR/'compare.py',parent/'state.json',MR/'receipt.json',MR/'session-observation.json'] :pin(p)
for label,key in [('author','author'),('peer','peer')]:
 p=TR/(label+'.json');pin(p);x=json.loads(p.read_text());assert x['observed_exit_code']==0 and x['state_sha256']==rec[key+'_state_sha256'] and term[key+'_terminal_sha256']==H(p)
for p,h in m22['gate_guard'].items():assert H(p)==h;gate[p]=h
for run in mt['runs']:
 for row in run['rows']:
  pin(MR/run['label']/'src/DiophantineConsistency'/(row['module']+'.lean'));pin(MR/run['label']/'logs'/(row['module']+'.log'))
  p=Path(run['run'])/'lib/DiophantineConsistency'/(row['module']+'.olean');pin(p);assert H(p)==row['object_sha256']
inv=dict(m22['parent_inventory'])
for row in state['records']:
 pin(parent/'logs'/(row['module']+'.log'));assert H(parent/'logs'/(row['module']+'.log'))==row['log_sha256']
 p=parent/'lib/DiophantineConsistency'/(row['module']+'.olean');assert H(p)==row['object_sha256'];inv[str(p.relative_to(parent/'lib'))]={'sha256':row['object_sha256'],'resolved_path':str(p)}
for a,b in zip(rec['matched_rows'],state['records']):assert a['module']==b['module'] and a['object_sha256']==b['object_sha256'] and a['log_sha256']==b['log_sha256']
assert inv['DiophantineConsistency/AdaptiveNamedValues33.olean']['sha256']==m22['model_object_sha256']
order=['AdaptiveNamedValues42','AdaptiveNamedValues42Checks','IPRANamedValues42Native','IPRANamedValues42NativeChecks'];sources={}
for n in order:
 p=SRC/(n+'.lean');raw=p.read_bytes();sources[n]={'sha256':H(p),'imports':re.findall(r'^import\s+([A-Z][\w.]*)',raw.decode(),re.M)}
 for suffix in ('.olean','.olean.private','.olean.server','.ir','.ilean'):
  assert not os.path.lexists(parent/'lib/DiophantineConsistency'/(n+suffix))
for n in order[:2]:assert sources[n]['sha256']==mt['base']['sources'][n]
O.mkdir();snap=O/'sources/DiophantineConsistency';snap.mkdir(parents=True)
for n in order:(snap/(n+'.lean')).write_bytes((SRC/(n+'.lean')).read_bytes())
(O/'replay.py').write_bytes((D/'replay.py').read_bytes());(O/'prepare.py').write_bytes(Path(__file__).read_bytes())
out={'status':'FOCUSED_NAMED42_INPUT','workspace_root':str(R),'parent':str(parent),'parent_inventory':inv,'inherited_manifest':pm,'gate_guard':gate,'model_guards':m22['model_guards']+[row['guards'] for row in state['records']]+[run['guards'] for run in mt['runs']],'sources':sources,'order':order,'lean_sha256':pm['lean_sha256'],'driver_sha256':H(O/'replay.py'),'preparer_sha256':H(O/'prepare.py'),'model_object_sha256':mt['runs'][1]['rows'][0]['object_sha256'],'boundary':'Four source-directed modules on the historical native-33 peer provider. Native-33 is supported by two matched suffix replays; the 42-variable model object must equal its separate matched model replay. Original 258-module project ancestry, 848 author-only ancestry, package-transitive ancestry and dynamic imports remain inherited; this is not a full current-source closure.'}
(O/'manifest.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print('PASS_INPUT',H(O/'manifest.json'),flush=True)
