#!/usr/bin/env python3
"""No-Lean artifact, guard and statement audit of contextual exclusion pair."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';R=BASE/'research/ordinary12-ipra-bridge';PKG=R/'compact44-model-noextra-prototype';OUT=Path('/tmp/ipra-compact-noextra-contextual-pair-01');PARENT=Path('/tmp/ipra-compact-row-transport-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');PRE=BASE/'reviews/compact44-contextual-output-guard-independent-audit';HERE=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
for n in subprocess.run(['git','show','--format=','--name-only','23ad82420b'],cwd=ROOT,check=True,capture_output=True,text=True).stdout.splitlines():
 blob=subprocess.run(['git','show','23ad82420b:'+n],cwd=ROOT,check=True,capture_output=True).stdout;need(hashlib.sha256(blob).hexdigest()==H(ROOT/n),'evidence drift '+n)
need(H(PKG/'contextual-replay.py')=='4e05a8a80989fc49fbd5a03f31f55e8e4681624d2520f3e9ba4a59fa36135913','driver hash')
need(H(PRE/'CHECK.json')=='94d0424cd5215536ddf19e412cac3002def80e753571262fe0816a21e6817ae3' and json.loads((PRE/'CHECK.json').read_text())['status']=='PASS_INDEPENDENT_CONTEXTUAL_OUTPUT_GUARD_PREFLIGHT','prelaunch receipt')
receipt_hash='a8f0544afb7abad7c669240abe0832a57099e2c84c2bcb27a1f53445c437037e';ev=PKG/'evidence-contextual'
need(H(ev/'receipt.json')==H(OUT/'receipt.json')==receipt_hash,'receipt hash')
t=json.loads((ev/'terminal-observation.json').read_text());need(t=={'historical_view':'/tmp/ipra-historical-audit-review-01','observed_exit':0,'protected_head':'73ad8806e1684415cc759ca57cce7361ce1ada01','receipt_sha256':receipt_hash,'session_id':82898,'status':'PASS_CONTEXTUAL_COMPACT_MODEL_NOEXTRA_PAIR'},'outer observation')
r=json.loads((ev/'receipt.json').read_text());need(r['status']==t['status'] and r['contextual_historical_view']==t['historical_view'] and len(r['rows'])==4,'receipt status')
need(r['driver_sha256']==H(PKG/'contextual-replay.py'),'driver receipt')
expected_parents=['PASS_INDEPENDENT_COMPACT_ROW_MATCH_AUDIT','PASS_INDEPENDENT_COMPACT44_FORBIDDEN_AUDIT'];need(r['parent_audit_before']==r['parent_audit_after']==expected_parents,'contextual parent statuses')
need(json.loads((ev/'progress.json').read_text())==json.loads((OUT/'progress.json').read_text())==r['rows'],'progress rows')
srcs={'CompactForbidden':R/'compact44-color-relabel/CompactForbidden.lean','CompactNoExtra':PKG/'CompactNoExtra.lean'};src_hash={'CompactForbidden':'27786b8ec2cf08ccd81f3cdb8f0585adf76fbfacc8e993be310d4697ac01e020','CompactNoExtra':'fcf37774ceef70180a36d6779394367f6ad9c73fa04d0fe87e910bc1b372dfa5'}
need(r['source_sha256']==src_hash,'receipt sources')
for n,p in srcs.items():
 frozen=OUT/'src/DiophantineConsistency'/(n+'.lean');need(p.is_file() and frozen.is_file() and not frozen.is_symlink() and H(p)==H(frozen)==src_hash[n],'source '+n)
s=srcs['CompactNoExtra'].read_text();need('(hl : left < 943)' in s and 'compactField (fun t => t.2.2.1) left = compactField (fun t => t.1) current' in s and 'current ≠ 1' in s and '(hpos : 0 < N)' in s and '(hbound : ∀ j < N, b j < 943)' in s and "(heast : ∀ j < N, ∀ j' < N, (j' + 1) % N = j →" in s and '∀ j < N, b j ≠ 1' in s,'exact theorem premises')
pattern=r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$"
wanted={'CompactForbidden':[('CompactForbidden.no_east_five_all',set()),('CompactForbidden.west_five_extra_all',set()),('CompactForbidden.no_east_five',{'propext','Quot.sound'}),('CompactForbidden.west_five_extra',{'propext','Quot.sound'}),('CompactForbidden.five_cannot_have_left',{'propext','Quot.sound'})], 'CompactNoExtra':[(n,{'propext','Classical.choice','Quot.sound'}) for n in ('CompactNoExtra.extra_forbidden_with_left','CompactNoExtra.cyclic_excludes_extra')]}
expected_guards={str(PACKAGE/'Init')+s for s in ('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')};summaries=[]
suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
for side in ('author','peer'):
 lib=OUT/side/'lib';old=PARENT/side/'lib';base={p.relative_to(old) for p in old.rglob('*.olean')};actual={p.relative_to(lib) for p in lib.rglob('*.olean')};extra={Path('DiophantineConsistency')/(n+'.olean') for n in srcs};need(len(base)==1210 and not base&extra and actual==base|extra,'overlay inventory '+side)
 for rel in base:need((lib/rel).resolve()==(old/rel).resolve() and H(lib/rel)==H(old/rel),'parent object '+str(rel))
 for n in ('Compact943Data','CompactRowComplete','CompactForbidden','CompactNoExtra'):
  stem=lib/'DiophantineConsistency'/n
  expected_guards.update(str(stem)+s for s in suffixes)
 for name in ('CompactForbidden','CompactNoExtra'):
  row=next(x for x in r['rows'] if x['side']==side and x['module']==name);obj=lib/'DiophantineConsistency'/(name+'.olean');log=OUT/side/(name+'.log');copy=ev/side/(name+'.log');frozen=OUT/'src/DiophantineConsistency'/(name+'.lean')
  need(row['exit']==row['deps_exit']==0 and row['stop_reason'] is None and obj.is_file() and not obj.is_symlink(),'compiler exit/object '+name)
  need(H(obj)==row['object_sha256'] and H(log)==H(copy)==row['log_sha256'] and H(frozen)==row['source_sha256']==src_hash[name],'artifact hash '+name)
  output=log.read_text();need(not re.search(r'warning:|error:|\bsorryAx\b|\bsorry\b',output),'warning/admission '+name)
  reports=re.findall(pattern,output,re.M);need([[n,a] for n,a in reports]==row['axiom_reports'] and [n for n,_ in reports]==[n for n,_ in wanted[name]],'report names '+name)
  need(all({x.strip() for x in ax.split(',') if x.strip()}==want for (_,ax),(_,want) in zip(reports,wanted[name])),'axiom sets '+name)
  dep={str(PACKAGE/'Init.olean')};dep.add(str(lib/'DiophantineConsistency/Compact943Data.olean') if name=='CompactForbidden' else str(lib/'DiophantineConsistency/CompactRowComplete.olean'))
  if name=='CompactNoExtra':dep.add(str(lib/'DiophantineConsistency/CompactForbidden.olean'))
  need(set(row['deps_stdout'].splitlines())==dep and all(Path(p).is_file() for p in dep),'deps '+name)
  cmd=row['command'];need(cmd[1:4]==['-M4000','-j1','-DElab.async=false'] and cmd[-3]==str(frozen) and cmd[-1]==str(obj),'command '+name)
  summaries.append({'side':side,'module':name,'object_sha256':H(obj),'log_sha256':H(log)})
need(len(expected_guards)==90 and set(r['direct_guards'])==expected_guards,'exact guard slots')
for name,old in r['direct_guards'].items():
 p=Path(name)
 if old is None:need(not os.path.lexists(p),'unexpected companion '+name)
 else:need(p.is_file() and str(p.resolve())==old['realpath'] and H(p)==old['sha256'],'guard drift '+name)
need(summaries[0]['object_sha256']==summaries[2]['object_sha256'] and summaries[0]['log_sha256']==summaries[2]['log_sha256'] and summaries[1]['object_sha256']==summaries[3]['object_sha256'] and summaries[1]['log_sha256']==summaries[3]['log_sha256'],'paired mismatch')
obs=json.loads((HERE/'parent-rerun-observation.json').read_text());need(obs=={'session_id':67039,'observed_exit':0,'historical_view':'/tmp/ipra-historical-audit-review-01','lean_launched':False},'review parent observation')
print(json.dumps({'status':'PASS_INDEPENDENT_CONTEXTUAL_EXCLUSION_ARTIFACT_AUDIT','evidence_commit':'23ad82420b','receipt_sha256':receipt_hash,'recorded_outer_session':82898,'recorded_outer_exit':0,'independent_parent_session':67039,'independent_parent_exit':0,'guard_slots_checked':90,'parent_objects_per_side':1210,'rows':summaries,'scope':'Contextual historical-parent artifact audit; exclusion assumes a bounded left matching neighbor or positive period with bounded cyclic matching. No word construction, matching proof, retained-port/checker calibration, machine simulation or PRA theorem; point-in-time/package/resource limits remain.'},indent=2))
