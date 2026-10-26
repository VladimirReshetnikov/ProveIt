"""Bind final height bytes to this round's completed isolated full rebuild.
This deliberately does not claim to execute another full final-archive rebuild.
The default public verifier must continue to run the complete height rebuild.
"""
import hashlib,json,sys
from pathlib import Path
root=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/release')
audit=Path(sys.argv[2]) if len(sys.argv)>2 else root/'audit'
def need(q,msg):
 if not q:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
binding=json.loads((audit/'HEIGHT_FINAL_BINDING.json').read_text())
snapshot=json.loads((audit/'HEIGHT_SNAPSHOT_BINDING.json').read_text())
need(sha(audit/'HEIGHT_SNAPSHOT_BINDING.json')==binding['snapshot_binding_sha256'],'snapshot inventory receipt bytes')
files=snapshot['files']|binding['added_non_input_receipts']
height=root/'height_one';actual={p.relative_to(height).as_posix() for p in height.rglob('*') if p.is_file()}
need(actual==set(files),'final height exact census')
for n,r in files.items():need((height/n).stat().st_size==r['bytes'] and sha(height/n)==r['sha256'],'exact replayed height bytes '+n)
replaydir=audit/'height_isolated_full'
for n,r in binding['evidence'].items():need((replaydir/n).stat().st_size==r['bytes'] and sha(replaydir/n)==r['sha256'],'isolated evidence bytes '+n)
prior=json.loads((replaydir/'REPLAY.json').read_text())
need(prior['status']=='PASS' and prior['original_files_unchanged'] and not prior['modified_files'] and not prior['created_files'],'successful immutable full snapshot replay')
commands={r['name']:r for r in prior['commands']}
need(set(commands)=={'isolation_preflight','height_normal_full','height_optimized_full'} and all(r['exit_code']==0 for r in commands.values()),'required full two-mode commands')
need(commands['height_normal_full']['argv']==['python3','-B','verify.py','--single'],'normal full actual builder')
need(commands['height_optimized_full']['argv']==['env','PYTHONOPTIMIZE=1','python3','-O','-B','verify.py','--single'],'optimized environment propagates to actual builders')
need(prior['initial_files']==len(snapshot['files']),'snapshot exact census evidence')
print(json.dumps({'status':'PASS','exact_replayed_files':len(snapshot['files']),'added_non_input_receipts':binding['added_non_input_receipts'],'full_snapshot_commands':prior['commands'],'evidence':binding['evidence'],'boundary':'This round23 final extracted height component has the exact141 previously full-rebuilt executable/proof/source/config/coefficient/certificate bytes, plus2 separately hashed non-input author receipts. The full normal and optimized run occurred in the prior mount/PID-isolated snapshot. This binding does not claim a fresh full final-archive height run; default verify_release.py still performs it.'},indent=2))
