from pathlib import Path
import hashlib,json
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency'
OUT=D/'research/arithmetic-pell-index-divisibility-accepted-integral-solution.json';pins={};observations=0

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
plan=fixed('research/arithmetic-pell-index-divisibility-cache-plan.json','ab6f041ac993f09ef46965feb906c3445da26d9c509a13ca7522c1b4a57a8274')
proposal=fixed('research/arithmetic-pell-index-divisibility-plan.md','9d6884265c4302389403316f795c7d37d5a27acdd36ac40ce8067919dc3d3a4b')
receipt=fixed('reviews/arithmetic-pell-integral-solution-root.md','6b5439f786a179cfc66e37b661472e3c40b406ac2ca05fe6b0e6f4cf95bd2bf0')
packet=fixed('reviews/arithmetic-pell-integral-solution-root-replay.json','21a3bb7db5291ac78fe2187baae7effecde46f52be7c6e4ef1f75044dc91dff5')
manifest=fixed('reviews/arithmetic-pell-integral-solution-root-replay/FILES.json','51d6c93972dbab55d574f19fb5f42992b432b1c5ef7588165da85f6e7eb6db02')
for item in json.loads(Path(manifest['path']).read_text()):check(dict(item,path=str(R/item['path'])))
p=json.loads(Path(plan['path']).read_text());q=json.loads(Path(packet['path']).read_text())
require(q['status']=='PASS' and q['compiler_invocations']==2 and q['reports']==5,'accepted replay')
for item in p['pins']:check(item)
for row in q['records']:
    require(row['exit_code']==0 and row['author_object_and_full_log_equal'],'byte-identical replay')
    for field in ['source','snapshot','object','log','timing']:check(row[field])
for field in ['author','state','durable_state','driver','final_authentication']:check(q[field])
module='DiophantineConsistency.ArithmeticPellIntegralSolution'
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
    pins=list(pins.values()),scope='Replace only provisional IntegralSolution provider path with independently accepted byte-identical ROOT provider. Preserve all original inventory/proposal bytes. Future leaf builds require separate ROOT launch check; zero dependencies refreshed.')
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(supplement=rec(OUT),observations=observations,unique_paths=len(pins)),indent=2))
