#!/usr/bin/env python3
"""Verify four fresh-model helper receipts and the failed combined split, without Lean."""
import pathlib,json,hashlib,os
D=pathlib.Path(__file__).resolve().parents[2];R=D/'research'
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(pathlib.Path(p).read_text())
cs=[('thirteen-current2011-carrier-split-draft/attempt01',58572,0,'PASS','023005d35e7c8a460213270f9b7ec013954b1010c9d80945db918baee919d319'),('thirteen-current2011-carrier-split-draft/attempt02',67406,1,'FAILED',None),('thirteen-current2011-carrier-model-prelude-diagnostic/attempt01',66728,0,'PASS','918f5fc28b61155bfc417f5ce50d1a5fde0023198c1b3779937768bbb9414bff'),('thirteen-current2011-core-invariants-draft/attempt01',3181,0,'PASS','3a4a7d8b04de145836ef2ccdfdd6cdf84cfc4c728caf5a4ec64785eb85c1a467'),('thirteen-current2011-rank-ordinate-draft/attempt01',35425,0,'PASS','07fe448925823258ff75480a6bc775eb2b46566654c67906f97a8be59052b6f7')]
out=[]
for name,session,outer,status,objhash in cs:
 p=R/name; d=load(p/'state.json');o=load(p/'outer-terminal.json')
 assert (d['status'],o['actual_session'],o['exit_code'])==(status,session,outer)
 assert [x['exit'] for x in d['runs']]==([0,0] if status=='PASS' else [0,-6])
 for run,log in zip(d['runs'],['deps.txt','compile.txt']): assert sha(p/log)==run['log_sha256']
 if status=='PASS':
  assert d['preflight_before_sha256']==d['preflight_after_sha256']
  assert d['object_sha256']==objhash
  cmd=d['runs'][-1]['command'];assert sha(cmd[cmd.index('-o')+1])==objhash
 else: assert 'memory_exception' in (p/'compile.txt').read_text()
 for key,v in d['direct_guard'].items():
  pp=pathlib.Path(key)
  if v is None: assert not os.path.lexists(pp),pp
  else: assert pp.is_file() and str(pp.resolve())==v['realpath'] and sha(pp)==v['sha256'],pp
 for key,v in d.get('overlay_links',{}).items():
  pp=pathlib.Path(key);assert pp.is_symlink() and str(pp.resolve())==v,(pp,v)
 out.append({'packet':name,'session':session,'outer_exit':outer,'child_exits':[x['exit'] for x in d['runs']],'guard_slots':len(d['direct_guard']),'overlay_links':len(d.get('overlay_links',{})),'state_sha256':sha(p/'state.json')})
pins={'thirteen-current2011-carrier-split-draft/src/DiophantineConsistency/ModelThirteenCarrierCore.lean':'394d7b25748bb93ac285f6bac763d948364ce12277a6ccf999dc6915f3864dc9','thirteen-current2011-carrier-model-prelude-diagnostic/ModelThirteenCarrierPrelude.lean':'c3a5c6047f9f72d7d5663fa2ad047f00754b5ea92208b6a04ae997714124acc8','thirteen-current2011-core-invariants-draft/ModelThirteenCoreInvariants.lean':'2e30e6042941ac449c68e1db49cc2aee818098a823e1c2e51a81198671d3e9c8','thirteen-current2011-rank-ordinate-draft/ModelThirteenRankOrdinate.lean':'5809fb104c3c59e973c967d901c58ad6546ae463a225e8ec9a9e080751f620f2'}
for name,h in pins.items(): assert sha(R/name)==h,name
pre=(R/'thirteen-current2011-carrier-model-prelude-diagnostic/ModelThirteenCarrierPrelude.lean').read_text()
for s in ['theorem port0','theorem port1','theorem port2','theorem port3','theorem shifted_of_positive']: assert s in pre
assert 'theorem complete' not in pre
tail='end Model\nend DiophantineConsistency.ModelThirteenCarrier\n'
assert pre.endswith(tail)
remaining=(R/'thirteen-current2011-carrier-split-draft/src/DiophantineConsistency/ModelThirteenCarrier.lean').read_text()
assert remaining.startswith(pre[:-len(tail)])
original=(R/'thirteen-current2011-fresh-model/src/DiophantineConsistency/ModelThirteenCarrier.lean').read_text()
a,b=original.split('/-! ### Literal thirteen-coordinate syntax -/');c,d=b.split('/-! ### Completion in every model of `𝗜𝚺₁` -/')
assert (R/'thirteen-current2011-carrier-split-draft/src/DiophantineConsistency/ModelThirteenCarrierCore.lean').read_text()==a+'/-! ### Literal thirteen-coordinate syntax -/'+c+'end DiophantineConsistency.ModelThirteenCarrier\n'
assert remaining==a.replace('import FrontierBridge\n','import FrontierBridge\nimport DiophantineConsistency.ModelThirteenCarrierCore\n',1)+'/-! ### Completion in every model of `𝗜𝚺₁` -/'+d
inv=(R/'thirteen-current2011-core-invariants-draft/ModelThirteenCoreInvariants.lean').read_text()
for s in ['theorem core_invariants (w : Fin 14 → V) (hFq : w 1 < q w)',').q =',').Y =',').E =',').a =',').c =',').delta =',').rank =']: assert s in inv,s
rank=(R/'thirteen-current2011-rank-ordinate-draft/ModelThirteenRankOrdinate.lean').read_text()
for s in ['theorem rank_ordinate','InternalZero','ycoord (rank w) (X w * Y w + Y w)']: assert s in rank,s
print(json.dumps({'status':'PASS','scope':'Static source and receipt audit only: no Lean replay, full completion, endpoint or transitive rebuild.','checks':out},indent=2))
