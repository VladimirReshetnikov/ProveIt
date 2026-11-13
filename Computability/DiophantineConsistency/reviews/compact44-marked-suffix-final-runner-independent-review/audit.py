#!/usr/bin/env python3
"""Recheck retained synthetic controls and no-Lean source preflight."""
import hashlib,json,os,pathlib,re,sys
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site or os.environ.get('PYTHONOPTIMIZE'): raise RuntimeError('isolated non-optimized Python required')
P=pathlib.Path;root=P.cwd();b=root/'Computability/DiophantineConsistency';p=b/'research/ordinary12-ipra-bridge/compact44-marked-suffix-final-author-runner';plan=p.parent/'compact44-marked-suffix-final-source-plan';H=lambda x:hashlib.sha256(P(x).read_bytes()).hexdigest();obs=json.loads((p/'observations/terminal-observation.json').read_bytes());pre=P('/tmp/ipra-marked-final-review-preflight-01')
assert H(p/'replay.py')==obs['runner_sha256']=='d801e9fc26c028e134b1bd148044027adf8350613f3b849d2040cfe861476ee6'
assert H(p/'full-fake-controls.py')==obs['fake_control_sha256']=='18d1cf4b0a4f2b31b75655110319572cb4e017dd1afe022110746da8a31c38a2'
assert H(p/'focused-controls.py')=='a21f9e8ba2e6546157be40f7468671bf727c2fe67283a2bfa1f72754d2d331eb' and H(p/'warning-controls.py')=='5a72e00f41e71feb3c7156c9018f54ddb70e7d86a2c5a94bd7de04accf1feea2'
assert obs['preflight_exit']==0 and obs['preflight_session']==79376 and H(p/'observations/preflight-preflight.json')==obs['preflight_sha256']=='318cef9c65c637e6b4cc28b5d971db9d0105d8e6a77420329ab7691b00da9406'
assert (p/'observations/preflight.stderr').read_bytes()==b'' and not P('/tmp/final-runner-review-preflight.stderr').read_bytes()
assert H(p/'observations/preflight-closure-audit-before.stdout')==obs['closure_check_sha256']=='b55a08a7efa315baa2973bbed07b1d1c5e9276663cd55e42f4f1cbbe0ba51134'
assert P('/tmp/final-runner-review-focused.json').read_bytes()==(p/'observations/focused.json').read_bytes() and P('/tmp/final-runner-review-warning.json').read_bytes()==(p/'observations/warning.json').read_bytes()
a=json.loads((p/'observations/full-fake.json').read_bytes());fake=json.loads(P('/tmp/final-runner-review-fake.json').read_bytes());assert a['status']==fake['status']=='PASS_ISOLATED_22_CHILD_FAKE_WRAPPER' and a['runner_sha256']==fake['runner_sha256']==obs['runner_sha256'] and len(a['cases'])==len(fake['cases'])==38
expected={'audit-after-failure':'fake audit after','audit-before-failure':'fake audit before','closure-check-drift':'pinned input changed','closure-schema-failure':'closure schema mismatch','duplicate-report':'duplicate axiom report','extra-axiom':'unpermitted or empty axiom report','final-old-object-mutate':'slot changed','final-shadow-companion':'slot changed','final-source-mutate':'final source drift','identical-source-symlink':'frozen source drift','late-source-mutate':'frozen source drift','missing-output':'missing or linked output','missing-report':'axiom report names differ','nonzero':'child failed','old-object-mutate':'slot changed','output-companion':'unexpected output companion','package-companion':'slot changed','prior-scan-drift':'pinned input changed','redirect-directory':'slot changed','reviewed-candidate-drift':'candidate differs from reviewed scan','reviewed-source-drift':'source changed','shadow-companion':'slot changed','shadow-object':'slot changed','symlink-output':'missing or linked output','warning':'diagnostic rejected','wrong-deps':'dependency mismatch'}
expected.update({'final-missing-new-dep':'dependency mismatch','final-new-dep-mutate':'slot changed'})
expected.update({'plane-extra-warning':'diagnostic rejected','plane-changed-warning':'diagnostic rejected','plane-warning-wrong-path':'diagnostic rejected','plane-warning-sorry':'diagnostic rejected','strip-changed-warning':'diagnostic rejected','strip-extra-output':'diagnostic rejected','soundness-changed-warning':'diagnostic rejected'})
assert fake['cases']['final-missing-new-dep']['steps_seen']==21 and fake['cases']['final-new-dep-mutate']['steps_seen']==22
assert set(fake['cases'])==set(expected)|{'success','plane-warning','all-known-warnings'}
for n in ['success','plane-warning','all-known-warnings']:assert fake['cases'][n]==a['cases'][n]=={'accepted':True,'failure':None,'steps_seen':22}
for n,why in expected.items():assert fake['cases'][n]['accepted'] is False and why in fake['cases'][n]['failure'] and a['cases'][n]['accepted'] is False and a['cases'][n]['steps_seen']==fake['cases'][n]['steps_seen']
actual=json.loads((pre/'preflight.json').read_bytes());author=json.loads((p/'observations/preflight-preflight.json').read_bytes());assert actual['status']==author['status']=='READY_AUTHOR_ONLY_SUFFIX_NO_LEAN' and actual['source_count']==author['source_count']==22 and len(actual['direct_companion_slots'])==740 and len(actual['source_pins'])==22
assert actual['direct_inputs']['DiophantineConsistency.MarkedSuffixInventory']['DiophantineConsistency.CompactWordExistence']=={'kind':'produced','path':str(pre/'lib/DiophantineConsistency/CompactWordExistence.olean')}
# Fresh output path and Python interpreter differ; the complete remaining mapping must match.
def normalized(j,path):
 x=json.loads(json.dumps(j).replace(path,'/tmp/PREFLIGHT'));x['closure_audit_before']['command'][0]='PYTHON';return x
assert normalized(actual,str(pre))==normalized(author,'/tmp/ipra-marked-suffix-final-preflight-01')
assert actual['closure_audit_before']['exit_code']==0 and H(pre/'closure-audit-before.stdout')==actual['closure_audit_before']['stdout_sha256']=='b55a08a7efa315baa2973bbed07b1d1c5e9276663cd55e42f4f1cbbe0ba51134' and not (pre/'closure-audit-before.stderr').read_bytes()
assert not P('/tmp/final-runner-review-preflight.stderr').read_bytes() and json.loads(P('/tmp/final-runner-review-preflight.stdout').read_bytes())=={'status':'READY_AUTHOR_ONLY_SUFFIX_NO_LEAN','sources':22,'direct_slots':740}
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
print(json.dumps({'status':'PASS_NO_LEAN_FINAL_MARKED_SUFFIX_RUNNER_REVIEW','reviewed_commit':'2564d509e5','runner_sha256':H(p/'replay.py'),'fake_sha256':H(p/'full-fake-controls.py'),'author_preflight_sha256':H(p/'observations/preflight-preflight.json'),'independent_preflight_sha256':H(pre/'preflight.json'),'sources':22,'source_requested_axiom_reports':58,'seed_files':521,'direct_candidate_and_target_package_slots':740,'fake_cases':len(fake['cases']),'fake_failures_rejected':len(expected),'lean_launched':False},indent=2,sort_keys=True))
