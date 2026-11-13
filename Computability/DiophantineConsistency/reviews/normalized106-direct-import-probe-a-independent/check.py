#!/usr/bin/env python3
"""Check saved case-A receipts and 210-slot inventory; never runs Lean."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
RESEARCH=HERE.parents[1]/'research'
A=RESEARCH/'normalized106-direct-import-probe-a'
PROBE=RESEARCH/'normalized106-combined-import-probe'
DIRECT=RESEARCH/'nine-variable-external-matrix-preflight/direct-result.json'
STATE=Path('/tmp/current14-standard-fresh-build-20261104/state.json')
pins={'command.sh':'a960705f3a9ececd5912b05439383479cc85d4a1c544e641186aa611f072a401',
 'observe.py':'f4e44ebebfa2d08eb6e1c7c5d6476dbdc30006cdbb4656fdaf0c5f77ac1a2e3c',
 'observer.json':'f5e5af580eff37051b3c685b43066c7aab9b0143ce1337c52583c3c17ea5ab09',
 'terminal-observation.json':'2d73f6393ed3f905630cf14d828c37404380601c0003d1cbcb36448f8d8ef217',
 'post-direct-guards.json':'a733ec1fcf8810dabc676eebe7dcb601298e33dea99f469fefd3d741e62c1e03',
 'preflight-before.json':'bbeb1c0012b6f00824c43f445911a4e49a68e5fa698eb2a2e2a0ae24864d78ae',
 'preflight-after.json':'bbeb1c0012b6f00824c43f445911a4e49a68e5fa698eb2a2e2a0ae24864d78ae',
 'EndpointPlusExternal.lean':'31aa8357e3b93245b71ffb41ad8c83b9897e1271f83dc478b922eb9c6b10ba2e'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,m):
 if not v:raise ValueError(m)
for name,h in pins.items():need(sha(A/name)==h,'pin '+name)
need(sha(HERE/'lean.log')=='0178cfaf74fc97e3f55278c31707c6c69159ff46e80c68383ee22b09be93ae59' and (HERE/'lean.log').read_bytes()==b'True : Prop\n','Lean log')
need(sha(PROBE/'runner.py')=='ed5f3f1bf138e5ae3586dd9c7c1ae4b46b4f2065de7b9295e4c827b7cc935866','preflight runner')
need(sha(PROBE/'EndpointPlusExternal.lean')==pins['EndpointPlusExternal.lean'],'command source')
need(sha(DIRECT)=='8fc9a8a1978eecd0ddfb58928a5f2aa113a0a757dd4e7b63d1aeb120df76f787','direct evidence')
need(sha(STATE)=='f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014','base evidence')
expected='''import DiophantineConsistency.IPRAStandardCurrentEndpoint
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Order.Units

#check True
'''
need((A/'EndpointPlusExternal.lean').read_text()==expected,'source contents')
obs=json.loads((A/'observer.json').read_bytes());term=json.loads((A/'terminal-observation.json').read_bytes())
need((term['case_a']['session_id'],term['case_a']['exit_code'],term['observer']['session_id'],term['observer']['exit_code'])==(3797,0,98248,0),'outer exit receipts')
need((obs['status'],obs['samples'],obs['lean_samples'],obs['sampled_peak_lean_rss_bytes'],obs['minimum_available_bytes'])==('ANCHOR_EXITED',31,28,2831581184,18836709376),'observer metrics')
need(obs['error'] is None and not obs['sampled_lean_descendants'] and not obs['unexpected_direct_children'],'observer findings')
before=json.loads((A/'preflight-before.json').read_bytes());after=json.loads((A/'preflight-after.json').read_bytes())
need(before==after=={'status':'PASS_NO_LEAN_PREFLIGHT','guard_entries':210,'scope':'Direct path/companion inventory, no import or process launched.'},'pre/post summary')
need(term['before_preflight']['exit_code']==term['after_preflight']['exit_code']==term['later_post_guard_capture']['exit_code']==0,'preflight exits')
direct=json.loads(DIRECT.read_bytes());state=json.loads(STATE.read_bytes());saved=json.loads((A/'post-direct-guards.json').read_bytes())
roots=[Path('/tmp/current14-standard-fresh-build-20261104/lib'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
names=['DiophantineConsistency.IPRAStandardCurrentEndpoint','Foundation.Vorspiel.Matrix','Mathlib.Algebra.MvPolynomial.CommRing','Mathlib.Algebra.Order.Ring.Abs','Mathlib.Algebra.Order.Ring.Cone','Mathlib.Data.Int.Basic','Mathlib.Data.Int.Order.Units']
suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash']
expected_paths={str(root/(name.replace('.','/')+suffix)) for name in names for root in roots for suffix in suffixes}
need(set(saved)==expected_paths and len(saved)==210,'inventory dimensions')
for name in names:
 for i,root in enumerate(roots):
  for suffix in suffixes:
   p=str(root/(name.replace('.','/')+suffix));value=saved[p]
   if name!=names[0]:need(value==direct['guards_after'][p],'external guard '+p)
   elif i:
    need(value is None,'endpoint shadow '+p)
   else:
    baseline=state['outputs'][name][p]
    need((value is None and baseline is None) or (value is not None and baseline is not None and all(value[k]==baseline[k] for k in ('realpath','sha256'))),'endpoint guard '+p)
need(state['status']=='PASS' and direct['status']=='PASS_DIRECT_DEPS_NOT_IMPORT_CHECK','basis statuses')
print(json.dumps({'status':'PASS_SAVED_CASE_A_EVIDENCE','slots':210,'scope':'Saved receipts and later inventory; no Lean replay; before/after inventories are summarized only.'},sort_keys=True))
