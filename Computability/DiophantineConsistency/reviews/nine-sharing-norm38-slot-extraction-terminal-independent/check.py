#!/usr/bin/env python3
"""Read-only check of extraction attempt evidence; no Lean execution."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-norm38-slot-extraction-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-slot-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='860af97597203b418e45d0dfe22724996d1c8191cc0cb43946b56534ced7f09e'
assert sha(a/'Norm38SlotExtraction-compile.txt')=='9acbebccfb847b7d4409b7c4a296341ee44d7bf15d8ef89b7b637928a76de93d'
s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38SlotExtraction')" and len(s['rows'])==1
r=s['rows'][0];assert r['module']=='Norm38SlotExtraction' and r['source_sha256']=='7afacc8c1f2b9b0e1b443f346653c21dde511fe200e8296daf2ec2afd4ea38fc'
assert sha(q/'src/DiophantineConsistency/Norm38SlotExtraction.lean')==sha(out/'src/DiophantineConsistency/Norm38SlotExtraction.lean')==r['source_sha256']
assert r['deps']['exit']==0 and r['deps']['stop_reason'] is None
assert r['compile']['exit']==-15 and r['compile']['stop_reason']=='timeout' and r['compile']['timeout_seconds']==120
for typ in ('deps','compile'):
 x=r[typ];assert not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/('Norm38SlotExtraction-'+typ+'.txt'))==sha(out/('Norm38SlotExtraction-'+typ+'.txt'))==x['log_sha256']
text=(a/'Norm38SlotExtraction-compile.txt').read_text();assert 'error: unsolved goals' in text and 'ι (Fin.cons 1 w 15) = ι (w 14)' in text
assert 'object_sha256' not in r and not (out/'lib/DiophantineConsistency/Norm38SlotExtraction.olean').exists()
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:assert Path(path).is_file() and str(Path(path).resolve())==v['realpath'] and sha(path)==v['sha256']
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
expected={'DiophantineConsistency.NormAssignment38':'74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1','DiophantineConsistency.SharingNormSquares':'9b9ebd07fbfc3294bccee69a9d28c617d8999c2beaa53bf605c1e86372486762'}
for name,h in expected.items():
 v=r['dependencies'][name];assert sha(v['path'])==h==v['sha256'] and str(Path(v['path']).resolve())==v['realpath']
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==54394 and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
print(json.dumps({'status':'PASS_FAILED_ATTEMPT_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'compile_log_sha256':sha(a/'Norm38SlotExtraction-compile.txt'),'outer_author_record_sha256':sha(a/'outer-terminal-author-record.json'),'recorded_outer_session':54394,'recorded_outer_exit':1,'deps_exit':0,'compile_exit':-15,'compile_stop':'timeout after Lean errors','guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'Retained evidence and point-in-time guards; no Lean replay or independently observed historical outer exit.'},indent=2,sort_keys=True))
