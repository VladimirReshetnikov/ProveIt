#!/usr/bin/env python3
"""Freeze the focused 22-variable native endpoint and its historical provider."""
import hashlib,json,os,re,sys
from pathlib import Path
R=Path.cwd().resolve();V=R/'Computability/DiophantineConsistency/reviews'; SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
D=Path(__file__).resolve().parent; O=Path(sys.argv[1]).absolute(); assert not O.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
N=V/'ipra-rank17-native-replay-input'; VR=V/'ipra-rank17-native-verification'; MR=V/'adaptive-square-sums22-model-replay'
parent=Path('/tmp/ipra-rank17-native-n795r_ja'); pm=json.loads((N/'manifest.json').read_text()); state=json.loads((parent/'state.json').read_text()); rec=json.loads((VR/'receipt.json').read_text()); mt=json.loads((MR/'receipt.json').read_text())
assert state['status']=='PASS' and state['manifest_sha256']==H(N/'manifest.json') and rec['author_path']==str(parent) and rec['author_state_sha256']==H(parent/'state.json') and len(rec['matched_rows'])==14
assert mt['status']=='MATCHED_PASS' and len(mt['runs'])==2 and mt['runs'][0]['rows']==mt['runs'][1]['rows']
assert all(x['exit']==0 for run in mt['runs'] for x in run['rows'])
assert mt['runs'][1]['rows'][0]['object_sha256']=='5796085041dda6ff2d37f0c8bb55bd0c0c1674248ea6a608a9c2b3f60dbc2b4c'
gate={}
def pin(p):
 p=Path(p).absolute();assert p.is_file() and p.resolve()==p;gate[str(p)]=H(p)
for p in [N/'manifest.json',N/'prepare.py',N/'replay.py',VR/'receipt.json',VR/'terminal.json',VR/'run.log',parent/'state.json',MR/'receipt.json',Path(mt['runs'][1]['run'])/'lib/DiophantineConsistency/AdaptiveNamedValues22.olean'] :pin(p)
for kind in ('ipra-rank17-native-terminal-observations','ipra-rank17-native-comparator-terminal-observations'):
 for label in ('author','peer'):
  p=V/kind/(label+'.json');pin(p);x=json.loads(p.read_text());assert x['observed_exit_code']==0
  if 'comparator' in kind and label=='author':assert x['receipt_sha256']==H(VR/'receipt.json') and x['terminal_sha256']==H(VR/'terminal.json')
  if 'comparator' not in kind and label=='author':assert x['state_sha256']==H(parent/'state.json')
for p,h in pm['gate_guard'].items():assert H(p)==h;gate[p]=h
for p,h in pm['origin_guard'].items():assert H(p)==h;gate[p]=h
for run in mt['runs']:
 for row in run['rows']:
  pin(MR/run['label']/'src/DiophantineConsistency'/(row['module']+'.lean'));pin(MR/run['label']/'logs'/(row['module']+'.log'))
  p=Path(run['run'])/'lib/DiophantineConsistency'/(row['module']+'.olean');pin(p);assert H(p)==row['object_sha256']
inv=dict(pm['parent_inventory'])
for row in state['records']:
 p=parent/'lib/DiophantineConsistency'/(row['module']+'.olean');assert H(p)==row['object_sha256'];inv[str(p.relative_to(parent/'lib'))]={'sha256':row['object_sha256'],'resolved_path':str(p)}
for a,b in zip(rec['matched_rows'],state['records']):assert a['module']==b['module'] and a['object_sha256']==b['object_sha256'] and a['log_sha256']==b['log_sha256']
assert inv['DiophantineConsistency/AdaptiveRankWitness17.olean']['sha256']=='ebe4d0c00d19901b0074e090aa96e2c9372ae6fd9a3a577bf957c85fb3584083'
order=['AdaptiveNamedValues22','AdaptiveNamedValues22Checks','IPRANamedValues22Native','IPRANamedValues22NativeChecks'];sources={}
for n in order:
 p=SRC/(n+'.lean');raw=p.read_bytes();sources[n]={'sha256':H(p),'imports':re.findall(r'^import\s+([A-Z][\w.]*)',raw.decode(),re.M)}
 for suffix in ('.olean','.olean.private','.olean.server','.ir','.ilean'):
  assert not os.path.lexists(parent/'lib/DiophantineConsistency'/(n+suffix))
O.mkdir();snap=O/'sources/DiophantineConsistency';snap.mkdir(parents=True)
for n in order:(snap/(n+'.lean')).write_bytes((SRC/(n+'.lean')).read_bytes())
driver=(D/'replay.py').read_bytes();(O/'replay.py').write_bytes(driver);(O/'prepare.py').write_bytes(Path(__file__).read_bytes())
out={'status':'FOCUSED_NAMED22_INPUT','workspace_root':str(R),'parent':str(parent),'parent_inventory':inv,'inherited_manifest':pm,'gate_guard':gate,'model_guards':[run['guards'] for run in mt['runs']],'sources':sources,'order':order,'lean_sha256':pm['lean_sha256'],'driver_sha256':H(O/'replay.py'),'preparer_sha256':H(O/'prepare.py'),'model_object_sha256':mt['runs'][1]['rows'][0]['object_sha256'],'boundary':'Four source-directed modules on the historical native-17 author provider. Native-17 is supported by two matched replays; the 22-variable model object must equal its separate matched model replay. The original 258-module ancestry, 848 author-only ancestry, package-transitive ancestry and dynamic imports remain inherited; this is not a full current-source closure.'}
(O/'manifest.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print('PASS_INPUT',H(O/'manifest.json'),flush=True)
