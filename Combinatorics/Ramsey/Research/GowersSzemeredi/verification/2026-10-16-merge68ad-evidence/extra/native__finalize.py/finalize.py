from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,ast
R=Path('/home/codex/.codex/worktrees/9c9b/Proofs'); O=Path('/tmp/gowers-merge68ad-native-tools')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git','--no-optional-locks',*args],cwd=R)
rows=json.loads((O/'source-rows.json').read_text()); m=json.loads((O/'measurement.json').read_text())
tracked={x for x in git('ls-tree','-r','--name-only','-z',m['comparison_commit'],'--','Combinatorics/Ramsey/Lean','lib/openai-math/lean').decode().split('\0') if x.endswith('.lean')}
assert tracked=={row['path'] for row in rows.values()}
assert all(sha(R/row['path'])==row['sha256'] for row in rows.values())
commit='a87906dc3960604bc3a0b423868d392b43ba85c0';assert git('rev-parse','HEAD').decode().strip()==commit
assert git('status','--porcelain')==b''
inv='Combinatorics/Ramsey/gowers-proof-status.json';invsha='d416811dbefdfce7b96b7b0b10d9200422fca4688dc2e193b47c1a0c18d158bd'
assert sha(R/inv)==invsha
comparison=Path('/tmp/gowers-merge68ad-inventory-actual/comparison.json');assert comparison.is_file()
for n in ['common.py','capture.py','run.py','prepare.py']:ast.parse((O/n).read_text())
m['status']='Prepared committed merge validation plan; source-only measurements, no snapshot captured and no native invocation'
m['finalized_at']=datetime.now(timezone.utc).isoformat();m['merge_commit']=commit;m['inventory_generation_pending']=False
m['baseline_tracked_module_keyset_verified']=6021
m['current_all_source_hashes_rechecked_after_commit']=6021
m['current_inventory']={'path':inv,'sha256':invsha,'comparison':{'path':str(comparison),'sha256':sha(comparison)}}
m['limitations'][0]='Plan measurements describe committed merge source a87906dc3960604bc3a0b423868d392b43ba85c0; all 6,021 measured Lean source bytes were rechecked after the merge commit and inventory normalization.'
(O/'measurement.json').write_text(json.dumps(m,indent=2)+'\n')
(O/'README.txt').write_text('Merge68ad native validation preparation\n\nThis package was prepared without running or importing native/capture/source-guard helpers.\ncommon.py, capture.py and run.py are byte-identical to the reviewed NEXT829 package.\nplan.json is remeasured on the resolved Lean sources at merge commit '+commit+'.\nAll 153 changed production owners and 1,668 of 1,671 dependent consumers are covered.\nOnly the same three aggregate facades are excluded as native roots; they remain protected inputs.\nThe original 1/65/18 roots suffice; core/shared/supplemental module counts are 572/1915/351.\nInventory normalization has completed. No source snapshot was captured and no native checker was run.\nA new committed snapshot and sequential fresh validation chain are still required.\nThe old 5e5a native outcomes do not certify merged sources.\n')
freeze={p.name:sha(p) for p in sorted(O.iterdir()) if p.is_file() and p.name!='freeze.json'}
(O/'freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
print(json.dumps({'measurement_sha256':sha(O/'measurement.json'),'freeze_sha256':sha(O/'freeze.json'),'plan_sha256':sha(O/'plan.json'),'merge_commit':commit,'files':len(freeze)},indent=2))
for p in O.iterdir():
 if p.is_file():p.chmod(0o444)
