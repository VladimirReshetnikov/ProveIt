#!/usr/bin/env python3
"""Reviewer-authored literal/metadata comparisons only; imports no delivery code."""
from pathlib import Path
import hashlib,json,re
OUT=Path(__file__).parent
ROOT=Path('/tmp/zfc-compare-d584512002')
R=ROOT/'zfc-return242-20261018/zfc-return242-20261018'
B=ROOT/'zfc242-branch-borrowing-20261018/zfc242-branch-borrowing'
REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')
BASE=REPO/'Computability/BusyBeaver/Research/ZFC/candidate-combined243/zfc_combined243_old.tm'
A=Path('/tmp/zfc-intake-8c41b1fb7d/BusyBeaver_242_Research_2026-10-18/busybeaver242-research/runtime/survivor_1_old.tm')
C=Path('/tmp/zfc-intake-8c41b1fb7d/BusyBeaver_241_Companion_2026-10-18/busybeaver241-companion/runtime/candidate_1_old.tm')
checks=[]
def check(label,p):
 if not p:raise AssertionError(label)
 checks.append(label)
def desc(p):return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
def table(p):
 rows={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,r,w,d,n=line.split();key=(int(q),int(r))
  check('unique row '+str(p)+':'+str(key),key not in rows)
  rows[key]=(int(w),d,int(n))
 return rows
old,new,primary,cur=map(table,[BASE,R/'machine/zfc_return242_old.tm',A,C])
branch=table(B/'machine/zfc242_old.tm')
check('return and branch exact inherited bytes',(R/'machine/zfc_return242_old.tm').read_bytes()==(B/'machine/zfc242_old.tm').read_bytes())
check('return and branch exact canonical bytes',(R/'machine/zfc_return242.tm').read_bytes()==(B/'machine/zfc242.tm').read_bytes())
check('counts',list(map(len,[old,new,primary,cur]))==[486,484,484,482])
deleted=sorted(set(old)-set(new));changed=[{'row':list(k),'old':old[k],'new':new[k]} for k in sorted(set(old)&set(new)) if old[k]!=new[k]]
check('delete only 15',deleted==[(15,0),(15,1)])
check('change only 11/0 and 27/1',[x['row'] for x in changed]==[[11,0],[27,1]])
check('literal patch',new[11,0]==(0,'R',27) and new[27,1]==(1,'R',22))
def rename(t):
 f=lambda q:27 if q==15 else q
 return {(f(q),r):(w,d,f(n)) for (q,r),(w,d,n) in t.items()}
renamed=rename(primary)
for k in sorted(new):check('primary A isomorphism '+str(k),renamed[k]==new[k])
check('primary A domains',set(renamed)==set(new))
combo=dict(new)
del combo[39,0];del combo[39,1]
combo[17,0]=(0,'L',106);combo[17,1]=(1,'L',37)
combo[46,0]=(0,'R',17);combo[50,0]=(0,'R',17)
renamed241=rename(cur)
for k in sorted(combo):check('241 composition isomorphism '+str(k),combo[k]==renamed241[k])
check('241 composition domains',set(combo)==set(renamed241))
def incoming(t,target):return [{'row':list(k),'action':list(v)} for k,v in sorted(t.items()) if v[2]==target]
expected={18:[(12,0),(148,0)],47:[(33,0),(144,0),(167,0)],65:[(51,0),(81,0)],27:[(18,0),(47,0),(65,0)]}
for target,ks in expected.items():
 actual=incoming(old,target)
 check('old invariant incoming '+str(target),[tuple(x['row']) for x in actual]==ks)
 check('old invariant write/move '+str(target),all(x['action'][:2]==[0,'L' if target==27 else 'R'] for x in actual))
check('15 sole predecessor',[tuple(x['row']) for x in incoming(old,15)]==[(11,0)])
for target,ks in {17:[(12,1)],39:[(46,0),(50,0)]}.items():
 check('241 invariant in return table '+str(target),[tuple(x['row']) for x in incoming(new,target)]==ks)
 check('241 incoming writes '+str(target),all(x['action'][:2]==[1 if target==17 else 0,'R'] for x in incoming(new,target)))
# Check source-literal arrays, without invoking Lean or delivery generators.
src=(B/'formal/Tables242.lean').read_text()
for label,t in [('oldRows',old),('newRows',new)]:
 body=src.split('def '+label+' : Array (Option (Action × Action)) := #[',1)[1].split('\n]',1)[0]
 recovered={};indices=[]
 for line in body.splitlines():
  if not line.strip():continue
  m=re.fullmatch(r'\s*(none|some \(⟨(false|true), (false|true), (\d+)⟩, ⟨(false|true), (false|true), (\d+)⟩\)),? -- (\d+)',line)
  check(label+' parse '+line,m is not None)
  g=m.groups();q=int(g[7]);indices.append(q)
  if g[0]!='none':
   recovered[q,0]=(int(g[1]=='true'),'R' if g[2]=='true' else 'L',int(g[3]))
   recovered[q,1]=(int(g[4]=='true'),'R' if g[5]=='true' else 'L',int(g[6]))
 check(label+' indices complete',indices==list(range(256)))
 check(label+' literal dictionary exact',recovered==t)
audit=(B/'formal/Audit242.lean').read_text()
check('18 supplied probes',len(re.findall(r'^#print axioms ',audit,re.M))==18)
check('13 supplied callers',len(re.findall(r'^example\b',audit,re.M))==13)
check('explicit nondefault proof limits','set_option maxRecDepth 4096' in src and 'set_option maxHeartbeats 2000000' in src)
formal=json.loads((B/'evidence/formal/verification.json').read_text())
check('supplied formal input unchanged',formal['before']==formal['after'])
for name,h in formal['source_snapshots'].items():check('supplied formal snapshot '+name,desc(B/'formal'/name)['sha256']==h)
check('supplied formal census',len(formal['probes'])==18 and formal['typed_callers']==13)
check('supplied formal log exact',(B/'evidence/formal/Audit242.log').read_text()==formal['commands'][-1]['output'])
# This is a metadata binding, not an independent replay of the claimed PASS.
hr=table(B/'alternatives/source-rotation/h_rotation243_old.tm')
hd=[{'row':list(k),'old':old[k],'new':hr[k]} for k in sorted(old) if old[k]!=hr[k]]
check('H rotation only two physical rows',[x['row'] for x in hd]==[[142,0],[142,1]])
check('H rotation literal rows',hr[142,0]==(0,'R',72) and hr[142,1]==(1,'R',17))
combined_h=dict(combo);combined_h[142,0]=hr[142,0];combined_h[142,1]=hr[142,1]
check('H rotation adds only sound incoming17',all(x['action'][:2]==[1,'R'] for x in incoming(combined_h,17)))
check('H rotation leaves 39 deleted',not incoming(combined_h,39))
scanner=json.loads((R/'research/scanner-probe.json').read_text())
check('scanner finite counts',scanner['cases']==8390 and scanner['bad_case_count']==99)
check('scanner first context',scanner['bad_cases'][0]['pc']=='11101001001000000' and scanner['bad_cases'][0]['contexts'][0]['bits']=='01001')
read_rel={R:['README.md','report.tex','semantic-extensions.tex','formalism-comparison.tex','expanded-summary.tex','research/scanner_probe.py','research/scanner-probe.json','research/semantic-targets/semantic_targets.tex','research/semantic-targets/semantic_targets.py','research/semantic-targets/README.txt','research/local-search/generic-hole-lemma.tex'],B:['README.md','REPRODUCING.md','report.tex','formal-status.tex','formal/Tables242.lean','formal/BlockSimulation.lean','formal/Reduction242.lean','formal/Audit242.lean','formal/verify_formal.py','code/verify_reduction.py','alternatives/orientation/codec_transport.md','alternatives/orientation/orientation_control.py','alternatives/orientation/evidence.json','alternatives/source-rotation/source_rotation.tex','alternatives/source-rotation/source-verification.json','alternatives/source-rotation/affine-verification.json']}
inputs=[desc(BASE),desc(A),desc(C),desc(R/'machine/zfc_return242_old.tm'),desc(R/'machine/zfc_return242.tm'),desc(B/'machine/zfc242_old.tm'),desc(B/'machine/zfc242.tm')]+[desc(p/r) for p,rr in read_rel.items() for r in rr]
result={'status':'SOURCE_ONLY_MATHEMATICAL_AND_LITERAL_REVIEW_COMPLETE','reviewer_role':'Independent reader of both deliveries; author of the separate uncompiled primary-A Fold242 drafts, disclosed for comparison scope. No delivery/source execution.','scope':'Main ordinary proofs, relevant semantic/orientation/source-rotation appendices and supplied relative Lean source/metadata. Own literal parsing only; no supplied checker, simulator, compiler, checksum-manifest validation, or maintained edits.','inputs':inputs,'reviewer_source':desc(Path(__file__)),'static_comparisons':len(checks),'main_patch':{'deleted_state':15,'changed_rows':changed,'working_states':242,'return_branch_bytes_identical':True,'primary_A_isomorphism':{'rename':{'15':27},'all484_rows_and_targets_equal':True},'compose_current241':{'rows':482,'rename':{'15':27},'all_rows_and_targets_equal':True,'new_state_count':241,'not_240':True}},'mathematical_review':{'main_argument':'No mathematical blocker found. The old-only incoming-row invariant and positive 1/1 or 2/2,2/4 checkpoint blocks preserve every tape cell/head. Arbitrary function tapes from state95 are covered; blank input is a specialization.','clock':'t_new=t_old+2*k, where k counts exceptional zero blocks; k<=t_old/2, so t_new<=2*t_old. This is sharper accounting for the same machine as primary A.','calibration':'Ordinary calibration uses inherited combined243 theorem; no new internally formalized PA transport or closed binary endpoint follows from supplied relative Lean source alone.'},'secondary':{'return_tag_blind_mp':'Useful all-assignment semantic rule under irreflexivity and at least two objects, with intentional compiler failure preserved. No implemented lower-state calibrated machine. Pointwise and singleton countermodels are essential.','return_nip':'Membership-atom/odd-nonreflexive-equality refutation recognition is sound under all-assignment semantics; no measured state saving.','scanner':'99/8390 finite fixtures refute the particular sufficient scanner contraction premise; not an unbounded impossibility theorem.','source_rotation':{'physical_rows':hd,'four_source_rotations':'R5 transfer-plus-one normal form, source6459 to6455 leaves/8390 to8386 guards, no physical state deletion. Compatible protected incoming rows after both folds, but requires changed-source calibration and runtime evidence.','state_count_after_folds':241},'orientation':'Primitive recursive atomic codec involution is a useful semantic design freedom. Matched whole emitter totals268/270/269/267, not a current241 improvement; matrix code used as binder needs alpha transport and backend reachability/calibration remain open.'},'supplied_formal_evidence':{'record':desc(B/'evidence/formal/verification.json'),'reported_status':formal['status'],'reported_probes':18,'reported_callers':13,'reported_warnings':0,'relative_function_tape_scope':True,'fresh_replay_by_reviewer':False,'nondefault_limits':formal['resource_settings'],'per_module_120_seconds_not_shared':True,'not_our_default_resource_profile':True},'findings':[],'recommendation':'Continue current241 fold chain; do not count these equivalent folds as extra deletions. Preserve the semantic MP/NIP rule, sharper clock/full-function-tape proof, source H rotations and codec-orientation experiment as distinct research material.'}
(OUT/'review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'receipt':desc(OUT/'review.json'),'comparisons':len(checks),'main_table':desc(R/'machine/zfc_return242_old.tm')}))
