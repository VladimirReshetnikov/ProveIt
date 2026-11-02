#!/usr/bin/env python3
"""Point-in-time extension of the nine-source copy-support inventory."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
REPO=Path.cwd();ROOT=REPO/'Computability/DiophantineConsistency';BASE=ROOT/'research/ordinary12-ipra-bridge';PARENT=BASE/'compact44-copy-support-closure-plan';SOURCE=BASE/'compact44-period-copy-prototype/CompactPeriodCopy.lean';PREFIX=Path('/tmp/ipra-same-witness-saturation-pair-01')
REVIEW=ROOT/'reviews/compact44-copy-support-closure-independent-audit'
PINS={REVIEW/'audit.py':'22980782580d6ae4a170a3f39d9a61fa1ba551d78fcaca1d0713bcaf1f981d3a',REVIEW/'CHECK.json':'3a47e3192ad1d308c875b4e5fbb0395e9d76b682c68e7efd6a9f0f56098ec102',REVIEW/'terminal-observation.json':'4d7aa168ce098dbfb119cce0cf4103fd453fa57ef3840cfdbdbbd421866f5967',PARENT/'scan.py':'3fa7b4a2156b40ccd520974ae3df4a1b2486a63d3e0e5d16245a6210f1e33dda',PARENT/'scan.json':'9657990b478ede604fa876c17a6463b04c391513b0aea312072a7c7e231c0679',PARENT/'terminal-observation.json':'a798c4bf71dae162a4b2fa0407a47dc0ad137f2e33f12ebc49bbf7a5766add26',SOURCE:'784bae25f74d5e198cd056b4d92de1ac20ebf1bc66ec2dd48309bbc502c08dc9'}
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
for p,sha in PINS.items():need(p.is_file() and h(p)==sha,('pinned input drift',str(p)))
parent=json.loads((PARENT/'scan.json').read_bytes());obs=json.loads((PARENT/'terminal-observation.json').read_bytes())
need(parent['status']=='PRELIMINARY_COPY_SUPPORT_CLOSURE_NOT_A_BUILD' and len(parent['source_order'])==9 and obs['normal_scan_exit']==0 and obs['optimized_scan_exit']==1 and obs['lean_launched'] is False and obs['scan_sha256']==PINS[PARENT/'scan.json'],'parent scan schema')
run=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'scan.py')],cwd=REPO,capture_output=True,timeout=180);need(run.returncode==0 and not run.stderr and run.stdout==(PARENT/'scan.json').read_bytes(),('parent scan rerun',run.returncode,run.stderr))
review=json.loads((REVIEW/'CHECK.json').read_bytes());review_obs=json.loads((REVIEW/'terminal-observation.json').read_bytes())
need(review.get('status')=='PASS_INDEPENDENT_COPY_SUPPORT_SOURCE_CLOSURE' and review.get('reviewed_commit')=='0c758f7594' and review.get('source_modules')==9 and review.get('parent_objects_per_side')==146 and review.get('direct_slots')==60 and review.get('target_slots')==180 and review.get('init_slots')==10 and type(review_obs.get('observed_exit')) is int and review_obs['observed_exit']==0 and review_obs.get('lean_launched') is False and review_obs.get('check_sha256')==PINS[REVIEW/'CHECK.json'],'independent parent review schema')
rr=subprocess.run([sys.executable,'-I','-S','-B',str(REVIEW/'audit.py')],cwd=REPO,capture_output=True,timeout=180);need(rr.returncode==0 and not rr.stderr and json.loads(rr.stdout)==review,('independent parent review rerun',rr.returncode,rr.stderr))
old=subprocess.run(['git','show',f'0c758f7594:{SOURCE.relative_to(REPO)}'],capture_output=True,check=True,timeout=15).stdout;need(hashlib.sha256(old).hexdigest()==PINS[SOURCE],'period source differs from committed bytes')
imports=[x[7:] for x in SOURCE.read_text().splitlines() if x.startswith('import ')];need(imports==['DiophantineConsistency.CompactCopySupport'] and parent['source_order'][-1]['module']==imports[0],'period direct import mismatch')
names=re.findall(r'^#print axioms\s+([^\s]+)',SOURCE.read_text(),re.M);need(names==['CompactPeriodCopy.period_index','CompactPeriodCopy.position_pos','CompactPeriodCopy.fixed_graph_period_copies'],'period report names')
slots={}
for side in ('author','peer'):
 stem=PREFIX/side/'lib/DiophantineConsistency/CompactPeriodCopy'
 for suffix in SUFFIXES:
  p=Path(str(stem)+suffix);need(not os.path.lexists(p),('period target collision',side,str(p)));slots[str(p)]=None
need(len(slots)==20,'period slots')
print(json.dumps({'status':'PRELIMINARY_TEN_SOURCE_PERIOD_COPY_CLOSURE_NOT_A_BUILD','parent_nine_scan_sha256':PINS[PARENT/'scan.json'],'parent_nine_review_sha256':PINS[REVIEW/'CHECK.json'],'parent_parent_audit_sha256':parent['parent_audit_sha256'],'source_order':parent['source_order']+[{'module':'DiophantineConsistency.CompactPeriodCopy','source':str(SOURCE),'source_commit':'0c758f7594','source_sha256':PINS[SOURCE],'imports':imports,'axiom_reports':names}],'inherited_objects':parent['objects'],'external_direct_slots':parent['external_direct_slots'],'previous_target_slots':parent['target_slots'],'period_target_slots':slots,'init_slots':parent['init_slots'],'scope':'Point-in-time source and object inventory only; fixed-symbolic graph zero, positive coordinates, arbitrary K and unproved retained-port/column/NoCarry/machine/iPRA links remain.'},indent=2,sort_keys=True))
