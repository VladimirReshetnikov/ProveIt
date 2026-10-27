from pathlib import Path
import hashlib,json
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency'
OUT=D/'research/arithmetic-pell-integral-solution-accepted-strong-divisibility.json';pins={};observations=0

def require(ok,msg):
    if not ok:raise RuntimeError(msg)
def rec(path):
    path=Path(path);data=path.read_bytes()
    return dict(path=str(path),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
def check(pin):
    global observations
    a=rec(pin['path']);require(a['sha256']==pin['sha256'],'hash '+pin['path'])
    if 'bytes' in pin:require(a['bytes']==pin['bytes'],'bytes '+pin['path'])
    pins[a['path']]=a;observations+=1;return a

def fixed(path,sha):return check(dict(path=str(D/path),sha256=sha))
require(not OUT.exists(),'new supplement')
plan=fixed('research/arithmetic-pell-integral-solution-cache-plan.json','27b365f34e47feeaaaa6e32c3987ed2cebbb3a6e333673c4d4717b52b3afcee2')
proposal=fixed('research/arithmetic-pell-integral-solution-plan.md','a99ddd196895b3dfabf41a976d9628e69481c308ab0dcef31a7abdcfda7e98a8')
receipt=fixed('reviews/arithmetic-pell-strong-divisibility-root.md','e98c3fa798cccc5b350851766f975f3e702a0403f001146a41578332597d43d2')
packet=fixed('reviews/arithmetic-pell-strong-divisibility-root-replay.json','d34855c8e44bbcd935d41d61eb3d0f85b412f0e5b36be46ba8bb67a4a143e3dc')
manifest=fixed('reviews/arithmetic-pell-strong-divisibility-root-replay/FILES.json','288af2b3758874436b9f828fa35af810f0a956e912a19c4801c82a34cc204bec')
for item in json.loads(Path(manifest['path']).read_text()):check(dict(item,path=str(R/item['path'])))
p=json.loads(Path(plan['path']).read_text());q=json.loads(Path(packet['path']).read_text())
require(q['status']=='PASS' and q['compiler_invocations']==2 and q['reports']==7,'accepted replay')
for item in p['pins']:check(item)
for row in q['records']:
    require(row['exit_code']==0 and row['author_object_and_full_log_equal'],'byte-identical replay')
    for field in ['source','snapshot','object','log','timing']:check(row[field])
for field in ['author','state','durable_state','driver','final_authentication']:check(q[field])
module='DiophantineConsistency.ArithmeticPellStrongDivisibility'
old=next(item for item in p['modules'] if item['module']==module)
new=next(item for item in q['records'] if item['module']==module)
require(old['source']==new['source'],'identical source record')
require(old['objects'][0]['sha256']==new['object']['sha256'],'identical object bytes')
check(rec(__file__))
for item in list(pins.values()):check(item)
result=dict(status='READ_ONLY_ACCEPTED_PROVIDER_SUPPLEMENT_NO_OVERLAY_OR_COMPILER',
    original_plan=plan,proposal=proposal,accepted_receipt=receipt,accepted_packet=packet,
    accepted_manifest=manifest,module=module,source=new['source'],old_object=old['objects'][0],
    accepted_object=new['object'],accepted_provider=q['private_provider'],
    counts=p['counts'],audit=rec(__file__),observations=observations,unique_paths=len(pins),
    pins=list(pins.values()),scope='Replace only provisional StrongDivisibility provider path with independently accepted byte-identical ROOT provider. Preserve all original inventory/proposal bytes. Future leaf builds require separate ROOT launch check; zero dependencies refreshed.')
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(supplement=rec(OUT),observations=observations,unique_paths=len(pins)),indent=2))
