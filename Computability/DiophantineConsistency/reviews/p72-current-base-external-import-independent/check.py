#!/usr/bin/env python3
import pathlib,json,hashlib,os
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/p72-current-base-external-import-probe';A=P/'attempt01';REPLAY=pathlib.Path(__file__).parent/'prior-preflight-replay.json'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
d=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal.json').read_text());assert sha(A/'state.json')=='1e5cea4e85ccdc05af1c0407ba4fd598965be89b9ae63604929fd44aeaa831a5' and (d['status'],o['actual_session'],o['exit_code'])==('PASS',29817,0)
assert sha(P/'run.py')==d['runner_sha256']=='145e37570b6b031f10af05f2d8e3d0cd29b28d44fce94842832bfa20426eae0f';assert sha(P/'P72ExternalImports.lean')=='084065e7503aca970b0874e12c83e78827ba03387143dbfb8e2ecdb129be5d83'
s=(P/'P72ExternalImports.lean').read_text();assert s=='import DiophantineConsistency.IPRAStandardCurrentEndpoint\nimport Mathlib.Algebra.MvPolynomial.CommRing\nimport Mathlib.Algebra.Order.Ring.Cone\nimport Mathlib.Data.Fintype.BigOperators\n\n#check True\n'
assert d['preflight_before']==d['preflight_after'] and sha(REPLAY)==d['preflight_before']['earlier_preflight_sha256']=='bbeb1c0012b6f00824c43f445911a4e49a68e5fa698eb2a2e2a0ae24864d78ae';r=json.loads(REPLAY.read_text());assert r['status']=='PASS_NO_LEAN_PREFLIGHT' and r['guard_entries']==210
assert len(d['preflight_before']['direct'])==150
for key,v in d['preflight_before']['direct'].items():
 p=pathlib.Path(key)
 if v is None:assert not os.path.lexists(p),p
 else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
expected=['DiophantineConsistency.IPRAStandardCurrentEndpoint','Mathlib.Algebra.MvPolynomial.CommRing','Mathlib.Algebra.Order.Ring.Cone','Mathlib.Data.Fintype.BigOperators'];assert set(d['dependencies'])==set(expected+['Init'])
assert d['dependencies'][expected[0]]['sha256']=='3b8abcafa1fad691d9a9005e2af8afae8bda77c7d761a00119ccea1c742dcbd2';assert d['dependencies'][expected[3]]['sha256']=='e9e47e19312252f1f7e73800173cc8e4a5001517a7f385665af244b0423c998e'
for n,v in d['dependencies'].items():p=pathlib.Path(v['path']);assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],n
for run,log in zip(d['runs'],['deps.txt','compile.txt']):
 assert sha(A/log)==run['log_sha256'] and run['exit']==0 and run['stop_reason'] is None and not run['monitor_errors'] and not run['observed_descendant_pids'] and '-M4000' in run['command']
 assert run['rss_limit_bytes']==5*1024**3 and run['host_floor_bytes']==10*1024**3 and run['timeout_seconds']==180 and run['sampling_interval_seconds']==0.1 and run['peak_session_rss_bytes']<5*1024**3 and run['min_host_available_bytes']>=10*1024**3
assert (A/'compile.txt').read_text()=='True : Prop\n' and set((A/'deps.txt').read_text().splitlines())=={v['path'] for v in d['dependencies'].values()}
assert sha('/tmp/p72-current-base-external-import-probe-20261105/P72ExternalImports.olean')==d['object_sha256']=='199e97968166803a7a03154c5b4f903554cee89b4301fefc4ba31d662f8bceb3'
print(json.dumps({'status':'PASS','outer_session':29817,'child_exits':[0,0],'direct_slots':150,'earlier_preflight_slots':210,'scope':'Single combined import and #check True; no P72 project build, transitive rebuild or Lean replay.'},indent=2))
