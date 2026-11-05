#!/usr/bin/env python3
"""Read-only audit of the failed static-to-seed check."""
import hashlib,json,os,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-norm38-static-to-seed-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-static-to-seed-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='ef56385cda7a7446ae21987dafcf253bd68539e435de252abcd77b75a1cd87f8';assert sha(a/'Norm38StaticToSeed-compile.txt')=='936f61a359484dc2290a04b412b99eef3d171780032221534a7968e8388b09cc'
s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38StaticToSeed')" and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Norm38StaticToSeed'
src=q/'src/DiophantineConsistency/Norm38StaticToSeed.lean';assert sha(src)==sha(out/'src/DiophantineConsistency/Norm38StaticToSeed.lean')==r['source_sha256']=='b7dafd1b3d9460ab2385efb8a6fae3d597be258139f98bc29d44e35d4a15a60f'
prior=(D/'research/nine-sharing-norm38-forward-bridge-draft/Norm38Forward.lean').read_text();find=lambda t:re.search(r'^theorem static_implies_seed_zero\b.*?(?=^/--|^end Model|^end DiophantineConsistency)',t,re.S|re.M).group().strip();assert find(src.read_text())==find(prior)
for typ in ('deps','compile'):
 v=r[typ];assert sha(a/('Norm38StaticToSeed-'+typ+'.txt'))==sha(out/('Norm38StaticToSeed-'+typ+'.txt'))==v['log_sha256'] and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids']
assert r['deps']['exit']==0 and r['compile']['exit']==1 and 'object_sha256' not in r and not (out/'lib/DiophantineConsistency/Norm38StaticToSeed.olean').exists()
log=(a/'Norm38StaticToSeed-compile.txt').read_text();assert 'error: Type mismatch: After simplification, term' in log and 'InternalZero e (Fin.cons 1 w)' in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:assert Path(path).is_file() and str(Path(path).resolve())==v['realpath'] and sha(path)==v['sha256']
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for v in r['dependencies'].values():assert Path(v['path']).is_file() and str(Path(v['path']).resolve())==v['realpath'] and sha(v['path'])==v['sha256']
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==24644 and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
print(json.dumps({'status':'PASS_FAILED_STATIC_TO_SEED_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'compile_log_sha256':sha(a/'Norm38StaticToSeed-compile.txt'),'author_recorded_outer_session':24644,'outer_exit':1,'direct_dependencies':len(r['dependencies']),'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'Retained failed compile and current direct-provider points; no Lean replay or independent historical outer observation.'},indent=2,sort_keys=True))
