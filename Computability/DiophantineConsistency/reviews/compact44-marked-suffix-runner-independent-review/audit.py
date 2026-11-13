#!/usr/bin/env python3
"""No-Lean review of suffix runner, retained synthetic controls and preflight."""
import hashlib,json,os,pathlib,re,sys
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('isolated non-optimized Python required')
P=pathlib.Path;root=P.cwd();b=root/'Computability/DiophantineConsistency';p=b/'research/ordinary12-ipra-bridge/compact44-marked-suffix-author-runner';plan=p.parent/'compact44-marked-suffix-source-plan';H=lambda x:hashlib.sha256(P(x).read_bytes()).hexdigest();obs=json.loads((p/'observations/observation.json').read_bytes());pre=P('/tmp/ipra-marked-suffix-independent-preflight-01');assert H(p/'replay.py')==obs['runner_sha256']=='853cc343163aaf962f840bf8ad1e60ba72c61592ce8fe9c88e668334d4780415' and H(p/'full-fake-controls.py')==obs['full_fake_controls_sha256']=='916e0b454130f3bed576bf973d36bb5d90c726d25a2c3446571bd1d3ae32b5a5' and H(p/'focused-controls.py')==obs['focused_controls_sha256']=='a21f9e8ba2e6546157be40f7468671bf727c2fe67283a2bfa1f72754d2d331eb'
assert obs['preflight']['actual_exit']==0 and obs['preflight']['session_id']==23750 and H(p/'observations/preflight.json')==obs['preflight']['receipt_sha256'] and obs['preflight']['receipt_sha256']=='8c8000dc1a0858997d67bc58166883b1c388615a098e14c2e161bd87a73e02c0'
assert (p/'observations/preflight-wrapper.stdout').read_text()==obs['preflight']['stdout'] and (p/'observations/preflight-wrapper.stderr').read_text()==obs['preflight']['stderr']==''
assert H(p/'observations/closure-audit-before.stdout')==obs['preflight']['closure_audit_stdout_sha256']=='91ed365da479a7ce7fe2e83651cfba486e8e5aa2a01ec6c055c7bca85640750e' and not (p/'observations/closure-audit-before.stderr').read_bytes()
assert P('/tmp/marked-suffix-independent-focused.json').read_text()==obs['focused_controls']['stdout'] and obs['focused_controls']['actual_exit']==0
old=(p/'observations/full-fake-02.log').read_text();fresh=P('/tmp/marked-suffix-independent-full-fake.json').read_text();assert hashlib.sha256(old.encode()).hexdigest()==obs['extended_full_fake']['log_sha256'];a=json.loads(old);fake=json.loads(fresh);assert a['status']==fake['status']=='PASS_ISOLATED_22_CHILD_FAKE_WRAPPER' and a['runner_sha256']==fake['runner_sha256']==obs['runner_sha256'] and len(a['cases'])==len(fake['cases'])==27
expected={'audit-after-failure':'fake audit after','audit-before-failure':'fake audit before','closure-check-drift':'pinned input changed','closure-schema-failure':'closure schema mismatch','duplicate-report':'duplicate axiom report','extra-axiom':'unpermitted or empty axiom report','final-old-object-mutate':'slot changed','final-shadow-companion':'slot changed','final-source-mutate':'final source drift','identical-source-symlink':'frozen source drift','late-source-mutate':'frozen source drift','missing-output':'missing or linked output','missing-report':'axiom report names differ','nonzero':'child failed','old-object-mutate':'slot changed','output-companion':'unexpected output companion','package-companion':'slot changed','prior-scan-drift':'pinned input changed','redirect-directory':'slot changed','reviewed-candidate-drift':'candidate differs from reviewed scan','reviewed-source-drift':'source changed','shadow-companion':'slot changed','shadow-object':'slot changed','symlink-output':'missing or linked output','warning':'diagnostic rejected','wrong-deps':'dependency mismatch'}
assert set(fake['cases'])==set(expected)|{'success'} and fake['cases']['success']=={'accepted':True,'failure':None,'steps_seen':22}
for n,why in expected.items():assert fake['cases'][n]['accepted'] is False and why in fake['cases'][n]['failure'] and a['cases'][n]['accepted'] is False and a['cases'][n]['steps_seen']==fake['cases'][n]['steps_seen']
actual=json.loads((pre/'preflight.json').read_bytes());author=json.loads((p/'observations/preflight.json').read_bytes());assert actual['status']==author['status']=='READY_AUTHOR_ONLY_SUFFIX_NO_LEAN' and actual['source_count']==author['source_count']==22 and len(actual['direct_companion_slots'])==740 and len(actual['source_pins'])==22
# Fresh output path and Python interpreter differ; the complete remaining mapping must match.
def normalized(j,path):
 x=json.loads(json.dumps(j).replace(path,'/tmp/PREFLIGHT'));x['closure_audit_before']['command'][0]='PYTHON';return x
assert normalized(actual,str(pre))==normalized(author,'/tmp/ipra-marked-suffix-preflight-draft-01')
assert actual['closure_audit_before']['exit_code']==0 and H(pre/'closure-audit-before.stdout')==actual['closure_audit_before']['stdout_sha256']=='91ed365da479a7ce7fe2e83651cfba486e8e5aa2a01ec6c055c7bca85640750e' and not (pre/'closure-audit-before.stderr').read_bytes()
assert not P('/tmp/ipra-marked-suffix-independent-preflight-01.stderr').read_bytes() and json.loads(P('/tmp/ipra-marked-suffix-independent-preflight-01.stdout').read_bytes())=={'status':'READY_AUTHOR_ONLY_SUFFIX_NO_LEAN','sources':22,'direct_slots':740}
for name,v in actual['direct_companion_slots'].items():
 q=P(name)
 if v is None:assert not os.path.lexists(q),name
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],name
rows=json.loads((plan/'source-scan.json').read_bytes())['sources']; assert len(rows)==22
for row in rows:
 f=(pre/'frozen'/P(*row['module'].split('.'))).with_suffix('.lean');assert f.is_file() and not f.is_symlink() and H(f)==row['sha256']==actual['source_pins'][str(f)] and H(P(row['source']))==row['sha256']
 stem=pre/'lib'/P(*row['module'].split('.'));assert all(not os.path.lexists(P(str(stem)+s)) for s in ('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash'))
assert sum(len(re.findall(r'^#print\s+axioms\s+([\w.]+)\s*$',P(row['source']).read_text(),re.M)) for row in rows)==58
seed=P(actual['seed']);
def files(p):
 d={}
 for x,dirs,fs in os.walk(p,followlinks=False):
  assert all(not P(x,y).is_symlink() for y in dirs)
  for y in fs:d[P(x,y).relative_to(p).as_posix()]=P(x,y)
 return d
src=files(seed);out=files(pre/'lib');assert len(src)==len(out)==521 and set(src)==set(out)
for key,val in src.items():assert out[key].is_symlink() and out[key].resolve()==val.resolve() and H(out[key])==H(val)
print(json.dumps({'status':'PASS_NO_LEAN_MARKED_SUFFIX_RUNNER_REVIEW','reviewed_commit':'9c9bc53cee','runner_sha256':H(p/'replay.py'),'fake_sha256':H(p/'full-fake-controls.py'),'author_preflight_sha256':H(p/'observations/preflight.json'),'independent_preflight_sha256':H(pre/'preflight.json'),'sources':22,'source_requested_axiom_reports':58,'seed_files':521,'direct_candidate_and_target_package_slots':740,'fake_cases':len(fake['cases']),'fake_failures_rejected':len(expected),'scope':'Author-only exploratory; synthetic controls and real no-Lean preflight, not compiled suffix, paired build, complete provider authentication or internal PRA theorem.','lean_launched':False},indent=2,sort_keys=True))
