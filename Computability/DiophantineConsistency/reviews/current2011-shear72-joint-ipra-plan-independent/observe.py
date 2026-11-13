#!/usr/bin/env python3
"""Read-only, point-in-time observations of selected frontier object candidates."""
import hashlib,json,os,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(30,30));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2];repo=root.parents[1]
def sha(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def obs(path):
 p=Path(path); exists=p.is_file()
 return {'path':str(p),'file_exists':exists,'is_symlink':p.is_symlink(),'resolved':str(p.resolve()),'sha256':sha(p) if exists else None}
proofs=[
 ('OrdinarySphere7160Generic','generic/attempt02','/tmp/current2011-ordinary71-60-generic-check02/OrdinarySphere7160Generic.olean','5808bcc7f662ff319ad6c64811260e216739888a7d4a8d89c68390d2561f9bae'),
 ('OrdinarySphere7160Literal','literal/attempt04','/tmp/current2011-ordinary71-60-literal-check04/OrdinarySphere7160Literal.olean','554fa13261dcb4f9535764871b4833d0b6182fab9503bfa27b3bc5f88d64d84a'),
 ('OrdinarySphere7160Model','model-join/attempt01','/tmp/current2011-ordinary71-60-model-join-check01/OrdinarySphere7160Model.olean','98eda3763aa05598820c567e52a4c89d51a3aaaeed2912a925a9c1560d20ef98'),
 ('OrdinarySphere7160IPRA','ipra/attempt01','/tmp/current2011-ordinary71-60-ipra-check01/OrdinarySphere7160IPRA.olean','a169a2e71e6699ef84f6196f43ef3bb54245208213cc32f776adadfa622f4421')]
out={}
for module,folder,path,source_sha in proofs:
 folder=root/('research/current2011-ordinary71-60-'+folder);res=folder/'result.json';outer=folder/'outer-observation.json'
 r=json.loads(res.read_bytes());o=json.loads(outer.read_bytes());z=obs(path)
 guards=[v for p,v in r['guards_before'].items() if p.endswith('/'+module+'.lean') and isinstance(v,dict)]
 z.update({'recorded_status':r['status'],'recorded_lean_exit':r['exit'],'recorded_outer_exit':o['observed_outer_exit'],'recorded_source_sha256':source_sha,'source_guard_matches':len(guards)==1 and guards[0].get('sha256')==source_sha,'recorded_object_sha256':r['object_sha256'],'object_matches_record':z['sha256']==r['object_sha256'],'guard_slots_recorded':len(r['guards_before']),'all_guard_slots_rechecked':False,'receipt_sha256':sha(res),'outer_observation_sha256':sha(outer)})
 out[module]=z
rpath=root/'research/current2011-ordinary94-six-module-build/attempt05/result.json';r=json.loads(rpath.read_bytes())
ex=obs('/tmp/current2011-ordinary94-six-overlay-20261105/lib/DiophantineConsistency/ArithmeticCarrier94Extraction.olean');private=obs('/tmp/current2011-ordinary94-six-overlay-20261105/src/DiophantineConsistency/ArithmeticCarrier94Extraction.lean')
workspace=obs(root/'Lean/DiophantineConsistency/ArithmeticCarrier94Extraction.lean')
ex.update({'recorded_object_sha256':r['object_sha256'],'object_matches_record':ex['sha256']==r['object_sha256'],'private_source':private,'workspace_source':workspace,'source_hashes_equal':private['sha256']==workspace['sha256'],'producer_receipt_sha256':sha(rpath),'recorded_status':r['status'],'recorded_exit':r['exit'],'transitive_ancestry_rechecked':False})
out['DiophantineConsistency.ArithmeticCarrier94Extraction']=ex
statep=Path('/tmp/current14-standard-fresh-build-20261104/state.json');state=json.loads(statep.read_bytes());record=next(x for x in state['records'] if x.get('module')=='DiophantineConsistency.ArithmeticPellFirstIndex')
z=obs('/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/ArithmeticPellFirstIndex.olean');z.update({'source_sha256_in_producer':record['source_sha256'],'selected_source_matches':record['source_sha256']=='8cf79ed14f00f565accbfae0eb03ccacca597d06d12a509fecd6d3272e30f9ce','recorded_object_sha256':record['object_sha256'],'object_matches_record':z['sha256']==record['object_sha256'],'recorded_compile_exit':record['exit'],'producer_state_sha256':sha(statep),'transitive_ancestry_rechecked':False});out['DiophantineConsistency.ArithmeticPellFirstIndex']=z
statep=root/'research/normalized106-fresh-base-model-build/attempt02/state.json';state=json.loads(statep.read_bytes());record=next(x for x in state['records'] if x.get('module')=='DiophantineConsistency.ModelDifferenceRing')
z=obs('/tmp/normalized106-fresh-model-build-v2-20261105/lib/DiophantineConsistency/ModelDifferenceRing.olean');z.update({'source_sha256_in_producer':record['source_sha256'],'selected_source_matches':record['source_sha256']=='5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998','recorded_object_sha256':record['object_sha256'],'object_matches_record':z['sha256']==record['object_sha256'],'recorded_compile_exit':record['compile']['exit'],'enclosing_build_status':state['status'],'producer_state_sha256':sha(statep),'transitive_ancestry_rechecked':False});out['DiophantineConsistency.ModelDifferenceRing']=z
out['DiophantineConsistency.HAExpressionNoZeroEquiv']={'sample':obs('/tmp/ipra-quartic-model-peer-8pzoji9_/lib/DiophantineConsistency/HAExpressionNoZeroEquiv.olean'),'source_producer_authenticated':False}
out['DiophantineConsistency.ModelCarrierSpheres']={'sample':obs('/tmp/ipra-thirteen-endpoint-successor-pair-01/author/lib/DiophantineConsistency/ModelCarrierSpheres.olean'),'source_producer_authenticated':False}
out['DiophantineConsistency.ZRows.CoprimeSquares']={'checked_paths':[obs('/tmp/current2011-ordinary94-six-overlay-20261105/lib/DiophantineConsistency/ZRows/CoprimeSquares.olean'),obs(repo/'.lake/build/lib/lean/DiophantineConsistency/ZRows/CoprimeSquares.olean')],'complete_filesystem_search':False,'source_producer_authenticated':False}
out['Mathlib']={'sample':obs(repo/'.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean'),'source_producer_authenticated':False}
print(json.dumps({'point_in_time_frontier_observations':out,'scope':'bounded paths and reported records only; does not authenticate load resolution, all guards, full ancestry or current proof; no Lean executed'},sort_keys=True,indent=2))
