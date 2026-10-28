from pathlib import Path
import hashlib,json
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency'
OUT=D/'research/arithmetic-pell-common-unit-accepted-gcd.json';pins={};observations=0

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
plan=fixed('research/arithmetic-pell-common-unit-cache-plan.json','7081d8c2bc515ea333aadb90fd3d6506643b09c26a5686f1f049c000438a0942')
proposal=fixed('research/arithmetic-pell-common-unit-plan.md','7ab5627b00a4c6fc0459978c6d4d7d58aff0b053d1dc69bb2a71e57c61d04402')
receipt=fixed('reviews/arithmetic-gcd-normalization-root.md','535322187b6410a60eed2c09d2ffaf715e6406781ebc0408d1c6ab1e74717d73')
packet=fixed('reviews/arithmetic-gcd-normalization-root-replay.json','b74df44673d2f89c82b6c85237c1e203a03296068dd0f6d455ecf4ad29d14512')
manifest=fixed('reviews/arithmetic-gcd-normalization-root-replay/FILES.json','b63ead412d73162dce5f37a2605776c3662c779382f45620d96f38831aa5a009')
for item in json.loads(Path(manifest['path']).read_text()):check(dict(item,path=str(R/item['path'])))
p=json.loads(Path(plan['path']).read_text());q=json.loads(Path(packet['path']).read_text())
require(q['status']=='PASS' and q['compiler_invocations']==2 and q['reports']==8,'accepted replay')
for item in p['pins']:check(item)
for row in q['records']:
    require(row['exit_code']==0 and row['author_object_and_full_log_equal'],'byte-identical replay')
    for field in ['source','snapshot','object','log','timing']:check(row[field])
for field in ['author','state','durable_state','driver','final_authentication']:check(q[field])
module='DiophantineConsistency.ArithmeticGcdNormalization'
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
    pins=list(pins.values()),scope='Replace only provisional Gcd provider path with independently accepted byte-identical ROOT provider. Preserve all original inventory/proposal bytes. Future leaf builds require separate ROOT launch check; zero dependencies refreshed.')
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(supplement=rec(OUT),observations=observations,unique_paths=len(pins)),indent=2))
