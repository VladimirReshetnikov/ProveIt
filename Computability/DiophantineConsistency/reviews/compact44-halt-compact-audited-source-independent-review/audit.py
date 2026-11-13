#!/usr/bin/env python3
"""No-Lean review of six-source halt-word closure on the audited author suffix."""
import hashlib,importlib.util,json,os,pathlib,re,sys
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('isolated nonoptimized Python required')
P=pathlib.Path;root=P.cwd();dc=root/'Computability/DiophantineConsistency';p=dc/'research/ordinary12-ipra-bridge/compact44-halt-compact-audited-plan';audit=dc/'reviews/compact44-marked-suffix-final-author-artifact-independent-audit';seed=P('/tmp/ipra-marked-suffix-final-build-01');pkg=P('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');H=lambda x:hashlib.sha256(P(x).read_bytes()).hexdigest()
for name,sha in [('scan.py','f7cf5cca9e0c7f124bea2bd7dec35978acecb88efb6fc869b9b3688fc5977a77'),('source-scan.json','a45508e7f15fca212f5be0db4055b15b01140d6a64ea2679eb65a9a9821d3585'),('diagnostic_policy.py','c971eee88522f81f6df9b813ca2ae979dd118ba9df56b2ccab76486d08c66b47'),('diagnostic-controls.py','26dd0f2d6e8e3fb2a6b5e685ffeae5726173de02347f31320068bd09e3be198a'),('diagnostic-controls.json','ef098eda7e6ea8ff683414fdd22e56d60e630fb64d1584d6ca4f97a29cebaf3d')]:assert H(p/name)==sha
assert P('/tmp/halt-audited-review-scan.json').read_bytes()==(p/'source-scan.json').read_bytes() and P('/tmp/halt-audited-review-controls.json').read_bytes()==(p/'diagnostic-controls.json').read_bytes() and b'invoke python3 -I -S -B without optimization' in P('/tmp/halt-audited-review-opt.stderr').read_bytes() and not P('/tmp/halt-audited-review-opt.stdout').read_bytes()
assert json.loads(P('/tmp/halt-audited-review-parent.json').read_bytes())==json.loads((audit/'CHECK.json').read_bytes()) and H(audit/'CHECK.json')=='5e9daa236d9925f30789488f65d5ad9a89516147231a1810577f78f873351d0e' and H(audit/'audit.py')=='3ef691af68a3065919a1da67539100898891781a73935ee65b23354db43409dc' and H(audit/'terminal-observation.json')=='2cf9a92f1a0d0a290d35958b094afb586404b9926d427d18c2d149da0b0480b8'
j=json.loads((p/'source-scan.json').read_bytes());assert j['status']=='PASS_POINT_IN_TIME_AUDITED_SUFFIX_HALT_SOURCE_SCAN' and j['lean_launched'] is False and H(seed/'RESULT.json')==j['seed_result_sha256']=='861109aea9162f2ba0573c640a0ba4dc1658e290ea7a620cdda39f1587695068' and H(seed/'preflight.json')==j['seed_preflight_sha256']=='e121b14ea08ad2f008ce9a85918704c419d5f6f6af0d58466dfc8be3e5f65495'
rows=j['sources']; names=['ArithmeticRunTrace','ArithmeticTilingTable','ArithmeticTilingRows','ArithmeticTilingBand','ArithmeticTilingWord','CompactHaltWord'];full=['DiophantineConsistency.'+n for n in names];assert [x['module'] for x in rows]==full
produced=set(); static=set()
for row in rows:
 source=root/row['source'];assert H(source)==row['sha256'] and not source.is_symlink() and re.findall(r'^import\s+([\w.]+)',source.read_text(),re.M)==row['imports']
 for dep in ['Init']+row['imports']:
  if dep not in produced:assert dep not in full;static.add(dep)
 produced.add(row['module'])
assert len(static)==5 and set(j['direct_candidates'])==static
assert rows[-1]['imports']==['DiophantineConsistency.ArithmeticTilingWord','DiophantineConsistency.CompactWordDefinability'] and H(p/'CompactHaltWord.lean')=='063ddd79f856d3e33ad16a6274289f14625c3e3935b415703aa74afc76f9526c'
suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def checkslots(dic):
 for name,v in dic.items():
  q=P(name)
  if v is None:assert not os.path.lexists(q),name
  else:assert q.is_file() and str(q.resolve(strict=True))==v['realpath'] and H(q)==v['sha256'],name
for module,candidates in j['direct_candidates'].items():
 assert [x['root'] for x in candidates]==[str(seed/'lib'),str(pkg)] and all(len(x['slots'])==10 for x in candidates)
 for candidate in candidates:
  assert set(candidate['slots'])=={str(P(candidate['root'])/P(*module.split('.')))+x for x in suffixes};checkslots(candidate['slots'])
 assert any(x['slots'][str(P(x['root'])/P(*module.split('.')))+'.olean'] is not None for x in candidates)
for module,candidates in j['target_slots'].items():
 assert module in full and [x['root'] for x in candidates]==[str(seed/'lib'),str(pkg)] and all(len(x['slots'])==10 and all(v is None for v in x['slots'].values()) for x in candidates)
 for candidate in candidates:
  assert set(candidate['slots'])=={str(P(candidate['root'])/P(*module.split('.')))+x for x in suffixes};checkslots(candidate['slots'])
assert len(j['target_slots'])==6 and sum(len(c['slots']) for cs in j['target_slots'].values() for c in cs)==120
history=dc/'reviews/ha87-isolated-full-author-pass';state=json.loads((history/'state.json').read_bytes());assert H(history/'state.json')==j['history_state_sha256']=='84c3bc6f6c34c47e67278c43df8580444d32e2946844a4c40c31cfd747f33a90'
assert set(j['diagnostic_baselines'])==set(names[:5]);spec=importlib.util.spec_from_file_location('diagnostic',p/'diagnostic_policy.py');policy=importlib.util.module_from_spec(spec);spec.loader.exec_module(policy)
for row in rows[:5]:
 name=row['module'].split('.')[-1];sourcepin,logpin,count=policy.EXPECTED[name];b=j['diagnostic_baselines'][name]; log=root/b['historical_log']; data=log.read_text();records=[x for x in state['records'] if x.get('module')==row['module'] and x.get('source_sha256')==sourcepin and x.get('exit')==0 and x.get('verified') is True];assert len(records)==1 and row['sha256']==sourcepin==b['source_sha256'] and H(log)==logpin==b['log_sha256']==records[0]['log_sha256'] and len(records[0]['warning_lines'])==data.count('warning:')==b['warning_count']==count and records[0]['log_file']==log.name
 current='/tmp/review/frozen/'+name+'.lean';replacement=data.replace(policy.HISTROOT+name+'.lean',current);assert policy.validate(name,sourcepin,current,replacement,data)['warning_count']==count
controls=json.loads((p/'diagnostic-controls.json').read_bytes());assert controls['status']=='PASS_NO_LEAN_DIAGNOSTIC_CONTROLS' and controls['total']==len(controls['checks'])==55 and controls['lean_launched'] is False
print(json.dumps({'status':'PASS_NO_LEAN_AUDITED_SUFFIX_HALT_SOURCE_REVIEW','reviewed_commit':'5b35381d4b','scan_sha256':H(p/'source-scan.json'),'source_count':6,'direct_modules':5,'direct_candidate_slots':100,'target_slots':120,'diagnostic_baselines':5,'diagnostic_controls':55,'parent_audit_rerun_exit':0,'parent_check_sha256':H(audit/'CHECK.json'),'scan_rerun_exit':0,'optimized_controls_exit':1,'lean_launched':False,'scope':'Uncompiled conditional client; single-author parent, point-in-time guard slots, inherited transitive/package ancestry unauthenticated; no graph zero, converse, retained tuple/K binding or internal PRA theorem.'},indent=2,sort_keys=True))
