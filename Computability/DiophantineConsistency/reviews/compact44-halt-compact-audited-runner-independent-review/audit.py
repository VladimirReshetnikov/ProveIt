#!/usr/bin/env python3
"""No-Lean review of halt-word exploratory runner and its controls."""
import hashlib,json,os,pathlib,sys
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('isolated nonoptimized Python required')
P=pathlib.Path;root=P.cwd();base=root/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';p=base/'compact44-halt-compact-audited-runner';plan=base/'compact44-halt-compact-audited-plan';ev=p/'observations';out=P('/tmp/ipra-halt-runner-review-preflight-01');H=lambda x:hashlib.sha256(P(x).read_bytes()).hexdigest()
for name,sha in [('replay.py','24334eb297fcfb592e3a55d83985f63a25802adae66de39923d5509b0cc34763'),('full-fake-controls.py','e6d4a1473d24793d14caedb0487af9fa666d1e4fef5d76d55887d87ca56bb36f'),('pin-controls.py','7aa2a64f6fefc79454049bb2a3f3af1ef112f8b81c0aca4fc3c1df84adb7883e')]:assert H(p/name)==sha
term=json.loads((ev/'terminal-observation.json').read_bytes());assert term['driver_sha256']==H(p/'replay.py') and term['fake']['observed_exit']==term['pin_controls']['observed_exit']==term['real_preflight']['observed_exit']==0 and term['optimized_controls']['observed_exit']==1 and all(x['lean_launched'] is False for k,x in term.items() if isinstance(x,dict))
assert H(ev/'full-fake.json')==term['fake']['stdout_sha256'] and H(ev/'pin-controls.json')==term['pin_controls']['stdout_sha256'] and P('/tmp/halt-runner-review-pin.json').read_bytes()==(ev/'pin-controls.json').read_bytes() and b'isolated nonoptimized Python required' in P('/tmp/halt-runner-review-opt.stderr').read_bytes() and not P('/tmp/halt-runner-review-opt.stdout').read_bytes()
old=json.loads((ev/'full-fake.json').read_bytes());fresh=json.loads(P('/tmp/halt-runner-review-fake.json').read_bytes());assert old['status']==fresh['status']=='PASS_SYNTHETIC_HALT_WRAPPER_CONTROLS' and old['cases']==fresh['cases']==29
expected={'nonzero':'child failed','shadow-object':'slot changed','shadow-companion':'slot changed','package-companion':'slot changed','previous-output-mutate':'slot changed','late-source-mutate':'final frozen drift','source-symlink':'frozen source drift','redirect-directory':'slot changed','symlink-output':'missing or linked output','missing-output':'missing or linked output','output-companion':'output companions','warning-modified':'diagnostic text mismatch','warning-missing':'warning count mismatch','warning-extra':'warning count mismatch','warning-wrong-path':'diagnostic text mismatch','sorry':'error or sorry','wrong-deps':'dependency mismatch','wrong-report':'client axiom report','extra-axiom':'unpermitted axiom set','missing-report':'client axiom report','audit-before-failure':'injected audit failure','audit-after-failure':'injected audit failure','closure-schema-boolean':'closure schema mismatch','parent-schema-invalid':'parent schema mismatch','scan-mismatch':'plan scan mismatch','audit-after-source-mutation':'final frozen drift','audit-after-shadow':'slot changed','audit-after-output-mutation':'slot changed'}
assert set(old['results'])==set(fresh['results'])==set(expected)|{'success'} and old['results']['success']==fresh['results']['success']=={'passed':True,'expected_pass':True,'rejection':None}
for name,why in expected.items():
 for result in (old['results'][name],fresh['results'][name]):assert result['passed'] is False and result['expected_pass'] is False and why in result['rejection'],(name,result)
a=json.loads((ev/'preflight-packaged.json').read_bytes());b=json.loads((out/'preflight.json').read_bytes());assert H(ev/'preflight-packaged.json')==term['real_preflight']['preflight_sha256']=='97529504e66dd0a29bece29fb3790f88421702f7278d6a5b2c638bb41035d8a4' and not P('/tmp/halt-runner-review-preflight.stderr').read_bytes() and json.loads(P('/tmp/halt-runner-review-preflight.stdout').read_bytes())=={'status':'READY_AUTHOR_HALT_COMPACT_NO_LEAN','sources':6,'guard_slots':160}
def norm(x,path):return json.loads(json.dumps(x).replace(path,'/tmp/PREFLIGHT'))
assert norm(a,'/tmp/ipra-halt-compact-preflight-03')==norm(b,str(out)) and b['status']=='READY_AUTHOR_HALT_COMPACT_NO_LEAN' and len(b['sources'])==len(b['sourceguards'])==6 and len(b['direct_companion_guards'])==160
assert b['parent_audit_before']=={'exit':0,'stdout_sha256':'5e9daa236d9925f30789488f65d5ad9a89516147231a1810577f78f873351d0e'} and b['closure_audit_before']=={'exit':0,'stdout_sha256':'b93af8ea96c6cab365bfa0e3d596a4fcbd473d914046a54d430de8611a156ad0'}
for name,v in b['direct_companion_guards'].items():
 q=P(name)
 if v is None:assert not os.path.lexists(q),name
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],name
rows=json.loads((plan/'source-scan.json').read_bytes())['sources'];assert b['sources']==rows
for row in rows:
 name=row['module'];f=(out/'frozen'/P(*name.split('.'))).with_suffix('.lean');assert H(f)==H(root/row['source'])==row['sha256']==b['sourceguards'][str(f)] and not f.is_symlink()
 stem=out/'lib'/P(*name.split('.'));assert all(not os.path.lexists(P(str(stem)+suffix)) for suffix in ('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash'))
last=b['inputs']['DiophantineConsistency.CompactHaltWord'];assert last['DiophantineConsistency.ArithmeticTilingWord']=={'kind':'produced','path':str(out/'lib/DiophantineConsistency/ArithmeticTilingWord.olean')} and last['DiophantineConsistency.CompactWordDefinability']['kind']=='static' and P(last['DiophantineConsistency.CompactWordDefinability']['record']['realpath']).is_relative_to(P('/tmp/ipra-marked-suffix-final-build-01/lib'))
def files(path):
 d={}
 for parent,dirs,fs in os.walk(path,followlinks=False):
  assert all(not P(parent,n).is_symlink() for n in dirs)
  for name in fs:d[P(parent,name).relative_to(path).as_posix()]=P(parent,name)
 return d
seed=files(P(b['seed']));actual=files(out/'lib');assert len(seed)==len(actual)==543 and set(seed)==set(actual)
for name,p0 in seed.items():assert actual[name].is_symlink() and actual[name].resolve()==p0.resolve() and H(actual[name])==H(p0)
print(json.dumps({'status':'PASS_NO_LEAN_AUDITED_HALT_COMPACT_RUNNER_REVIEW','reviewed_commit':'835743749d','runner_sha256':H(p/'replay.py'),'fake_sha256':H(p/'full-fake-controls.py'),'source_count':6,'guard_slots':160,'seed_files':543,'fake_cases':29,'injected_rejections':28,'parent_audit_exit':0,'closure_audit_exit':0,'preflight_exit':0,'optimized_controls_exit':1,'lean_launched':False,'scope':'Author-only no-Lean preflight and synthetic controls; inherited transitive/package/dynamic ancestry unauthenticated; no compiled client or internal PRA theorem.'},indent=2,sort_keys=True))
