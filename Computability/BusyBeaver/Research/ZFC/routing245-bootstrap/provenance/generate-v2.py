#!/usr/bin/env python3
"""Emit a bounded routing245 blank-run proof unit; generated checkpoints are untrusted.
This program simulates only when root explicitly invokes it. It never invokes
Lean, a proof guard, a compiler version query, a downloader or a dependency build.
First emit1024; then emit one actual16384 continuation to measure proof cost.
Subsequent depth lists are explicit, at most four blocks with depths at most14.
"""
from pathlib import Path
import argparse,hashlib,json,re
DEFAULT_REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')
TABLE_REL='Computability/BusyBeaver/Research/ZFC/candidate-routing245/zfc_routing245.tm'
TABLE_SHA='17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13'
FAST_REL='Computability/BusyBeaver/Research/ZFC/results/fast-table-routing245-verification.json'
FAST_SHA='b9aa533b7e04c59a382147b3c165c20e2366be008981e43695050e4ac705b09d'
END=407915

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
def desc(p):return dict(path=str(p),sha256=sha(p))
def dump(p,obj):p.write_text(json.dumps(obj,indent=2)+'\n')
def read_parent(p,module,pin=None):
 if pin:need(sha(p)==pin,'Selected parent record changed.')
 r=json.loads(p.read_text())
 need(r['status']=='PASS' and r['prepare_only'] is False and r['only_standard_axioms'] and
      r['source_object_recorded_before_audit'] and r['all_input_provider_postchecks'] and
      r['all_fresh_objects_unchanged_after_audit'] and r['before']==r['after'],'Incomplete parent evidence.')
 need([q['label']for q in r['commands']]==['source','audit'] and all(q['exit_code']==0 for q in r['commands']),'Parent commands failed.')
 for f,h in r['before'].items():need(sha(f)==h,'Stale selected parent input '+f)
 fresh=[q for q in r['fresh_modules']if q['module']==module];need(len(fresh)==1,'Wrong parent module.')
 q=fresh[0];need(all(q[k]==r['source_pass_object'][k]for k in ['module','path','sha256','source_sha256']),'Parent pre-audit object differs.')
 need(sha(q['path'])==q['sha256']==r['fresh_first_provider_before_audit']['sha256'],'Parent fresh object changed.')
 for role in ['source','audit']:
  need(sha(r[role]['path'])==sha(r[role]['snapshot'])==r[role]['sha256'],'Parent source/audit snapshot changed.')
 need(q['source_sha256']==r['source']['sha256'],'Parent source/object binding differs.')
 return r

def parse_table(p):
 need(sha(p)==TABLE_SHA,'Canonical table changed.');rows={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,t=line.split();q,b,w,t=map(int,[q,b,w,t]);need((q,b)not in rows and w in(0,1)and d in('L','R')and 0<=t<=245,'Invalid/duplicate action.')
  rows[q,b]=(w,d,t)
 need(set(rows)=={(q,b)for q in range(245)for b in(0,1)},'Expected all490 actions.')
 need(p.read_text().splitlines()[0]=='#! start 0','Wrong initial state.')
 return rows

def simulate(rows,times):
 """Independent sparse and finite-zipper representations; compare all checkpoints."""
 q=h=qs=hs=0;left=[];right=[];ones=set();saved={}
 for t in range(1,max(times)+1):
  need(q<245 and qs<245,'Unexpected halt before requested checkpoint.')
  w,d,qs=rows[qs,int(hs in ones)]
  if w:ones.add(hs)
  else:ones.discard(hs)
  hs+=1 if d=='R'else -1
  w,d,q=rows[q,right[0]if right else 0]
  if d=='R':left,right,h=[w]+left,right[1:],h+1
  else:right,left,h=[left[0]if left else 0,w]+right[1:],left[1:],h-1
  need((q,h)==(qs,hs)and q<245,'Sparse/zipper state/head mismatch or halt.')
  if t in times:
   support={h-i-1 for i,b in enumerate(left)if b}|{h+i for i,b in enumerate(right)if b}
   need(support==ones,'Complete sparse and zipper tape supports differ.')
   saved[t]=dict(state=q,head=h,left=left.copy(),right=right.copy(),ones=sorted(ones))
 return saved

def bits(xs):return ' ++\n      '.join('['+', '.join('true'if b else'false'for b in xs[i:i+96])+']'for i in range(0,len(xs),96))or'[]'
def conf(name,z):
 return f'''def {name} : ZipConfig 245 :=
  {{ state := some ⟨{z['state']}, by decide⟩, head := {z['head']},
    left := {bits(z['left'])},
    right := {bits(z['right'])} }}
'''
def parse_conf(text,name):
 match=re.search(r'def '+re.escape(name)+r' : ZipConfig 245 :=\s*\{(.*?)\n?\s*\}',text,re.S);need(match is not None,'Missing predecessor literal checkpoint.')
 s=match.group(1);left,right=s.split('left :=',1)[1].split('right :=',1)
 return dict(state=int(re.search(r'state := some ⟨(\d+),',s)[1]),head=int(re.search(r'head := (-?\d+)',s)[1]),left=[int(x=='true')for x in re.findall(r'\b(true|false)\b',left)],right=[int(x=='true')for x in re.findall(r'\b(true|false)\b',right)])

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,default=DEFAULT_REPO)
 p.add_argument('--kind',choices=['first','next'],required=True);p.add_argument('--output',type=Path,required=True)
 p.add_argument('--previous-record',type=Path);p.add_argument('--previous-inventory',type=Path)
 p.add_argument('--depths',type=int,nargs='+');a=p.parse_args();repo=a.repo.resolve();out=a.output.resolve()
 need(not out.is_relative_to(repo)and(not out.exists()or not any(out.iterdir())),'Use new empty external output.')
 table=repo/TABLE_REL;fast=repo/FAST_REL;read_parent(fast,'BusyBeaver.ZFC.FastTableRouting245',FAST_SHA)
 parents=[dict(**desc(fast),module='BusyBeaver.ZFC.FastTableRouting245')];metadata_inputs=[]
 if a.kind=='first':
  need(a.depths is None and a.previous_record is None and a.previous_inventory is None,'First unit accepts no predecessor/depth override.')
  index=0;start=0;depths=[10];ns='BootRouting245First';imports=['BusyBeaver.ZFC.FastTableRouting245','BusyBeaver.ZFC.FiniteZipper'];previous=None
 else:
  need(a.previous_record is not None and a.previous_inventory is not None,'A complete previous unit is required.')
  need(a.depths is not None and 1<=len(a.depths)<=4 and all(0<=x<=14 for x in a.depths),'Use one to four explicit depths in0..14.')
  ip=a.previous_inventory.resolve();previous=json.loads(ip.read_text());module=previous['module']
  previous_index=previous['unit_index'];need(isinstance(previous_index,int) and previous_index>=0,'Invalid predecessor index.')
  expected_module='BusyBeaver.ZFC.BootRouting245First' if previous_index==0 else f'BusyBeaver.ZFC.BootRouting245Chunk{previous_index:03d}'
  need(module==expected_module and previous['checkpoint_name']==f"checkpoint{previous['endpoint']}",'Unexpected predecessor module/checkpoint API.')
  expected_theorem='first1024' if previous_index==0 else f"reached{previous['endpoint']}"
  need(previous['actual_run_theorem']==expected_theorem and (previous_index!=0 or previous['endpoint']==1024),'Unexpected predecessor actual-run API.')
  rp=a.previous_record.resolve();r=read_parent(rp,module)
  need(previous['source']['sha256']==r['source']['sha256']and sha(previous['source']['path'])==r['source']['sha256'],'Inventory does not match checked predecessor.')
  need(previous['audit']['sha256']==r['audit']['sha256'],'Inventory audit differs.')
  index=previous['unit_index']+1;start=previous['endpoint'];need(1024<=start<END,'Invalid previous endpoint.')
  depths=a.depths;ns=f'BootRouting245Chunk{index:03d}';imports=[module]
  parents=[dict(**desc(rp),module=module)];metadata_inputs=[desc(ip)]
 segments=[];at=start
 for dep in depths:segments.append(dict(start=at,end=at+(1<<dep),depth=dep));at+=1<<dep
 need(at<=END,'Requested unit passes exact407915 target.')
 if a.kind=='next'and index==1:need(start==1024 and depths==[14],'First continuation must be the single16384 measurement.')
 times={s['end']for s in segments}|({start}if start else set());data=simulate(parse_table(table),times)
 if previous:
  literal=parse_conf(Path(r['source']['path']).read_text(),previous['checkpoint_name'])
  need(all(literal[k]==data[start][k]for k in literal),'Fresh independent predecessor data differ.')
 final=(at==END)
 if final:
  primary=[0,0,0,3,0,0,3,0,0];file=primary+[1]*167;regbits=[b for v in file for b in [0]+[1]*(v+1)]
  expected=dict(state=88,head=-5,left=[1]+[0]*9,right=[0]*181+[1]+regbits)
  need(all(data[END][k]==v for k,v in expected.items()),'Complete proposed dispatch frame differs.')
  need(len(data[END]['ones'])==351,'Unexpected complete final support size.')
 module='BusyBeaver.ZFC.'+ns
 source=''.join('import '+m+'\n'for m in imports)+f'''
/-! Exact routing245 blank-run continuation {start} to {at}.
Expected finite checkpoint data are untrusted input, discharged by kernel
reduction and whole-tape zipper soundness. Default proof limits apply.
Runtime framing, coverage and PA comparison are separate obligations. -/
namespace SetTheory.BusyBeaver.ZFC.{ns}
open FiniteZipper FastTableRouting245

'''
 probes=[];examples=[]
 if a.kind=='first':
  source+='''def checkpoint0 : ZipConfig 245 :=
  { state := some ⟨0, by decide⟩, head := 0, left := [], right := [] }

theorem checkpoint0_rep : ZipRep (initial 245) checkpoint0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro i <;> rfl

theorem advance_checkpoint (elapsed depth : Nat) {z z' : ZipConfig 245}
    (before : ZipRep (machineRouting245.run elapsed) z)
    (calculated : zipBlock fastMachine depth z = z') :
    ZipRep (machineRouting245.run (elapsed + 2 ^ depth)) z' := by
  rw [Machine.run_add_eq_runFrom]
  have h := zipBlock_sound fastMachine depth before
  rw [calculated, fastMachine_eq] at h
  exact h

'''
  prev_z='checkpoint0';prev_h='checkpoint0_rep';probes+=['checkpoint0_rep','advance_checkpoint'];examples+=['example : ZipRep (initial 245) checkpoint0 := checkpoint0_rep',"example (elapsed depth : Nat) {z z' : ZipConfig 245} (h : ZipRep (machineRouting245.run elapsed) z) (hc : zipBlock fastMachine depth z = z') : ZipRep (machineRouting245.run (elapsed + 2 ^ depth)) z' := advance_checkpoint elapsed depth h hc"]
 else:
  pn=previous['module'].rsplit('.',1)[1];prev_z=pn+'.'+previous['checkpoint_name'];prev_h=pn+'.'+previous['actual_run_theorem']
 for s in segments:
  t=s['end'];z=f'checkpoint{t}';h='first1024'if a.kind=='first'else f'reached{t}';b=f'block{t}';dep=s['depth']
  source+=conf(z,data[t])+f'''
theorem {b} : zipBlock fastMachine {dep} {prev_z} = {z} := by
  decide +kernel

theorem {h} : ZipRep (machineRouting245.run {t}) {z} :=
  BootRouting245First.advance_checkpoint {s['start']} {dep} {prev_h} {b}

'''
  probes.extend([b,h]);examples.extend([f'example : zipBlock fastMachine {dep} {prev_z} = {z} := {b}',f'example : ZipRep (machineRouting245.run {t}) {z} := {h}']);prev_z=z;prev_h=h
 if final:
  source+=f'''theorem bootstrap407915 : ZipRep (machineRouting245.run 407915) {prev_z} := {prev_h}

theorem bootstrap_active_through :
    ∀ elapsed, elapsed ≤ 407915 → (machineRouting245.run elapsed).state ≠ none := by
  apply active_through_of_endpoint
  rw [bootstrap407915.1]
  decide

'''
  probes+=['bootstrap407915','bootstrap_active_through'];examples += [f'example : ZipRep (machineRouting245.run 407915) {prev_z} := bootstrap407915','example (t : Nat) (h : t ≤ 407915) : (machineRouting245.run t).state ≠ none := bootstrap_active_through t h']
 source+=f'end SetTheory.BusyBeaver.ZFC.{ns}\n'
 examples += [f'example : (machineRouting245.run {at}).state = {prev_z}.state := {prev_h}.1',f'example : (machineRouting245.run {at}).head = {prev_z}.head := {prev_h}.2.1',f'example (p : Int) : Tape.read (machineRouting245.run {at}).tape p = frameRead {prev_z} p := read_eq_frameRead {prev_h} p']
 names=['SetTheory.BusyBeaver.ZFC.'+ns+'.'+n for n in probes]
 audit=f'import {module}\n\nopen SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC\nopen FiniteZipper FastTableRouting245 {ns}\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n\n'+'\n\n'.join(examples)+'\n'
 out.mkdir(parents=True,exist_ok=True);sp=out/(ns+'.lean');ap=out/'Audit.lean';dp=out/'data.json';sp.write_text(source);ap.write_text(audit)
 dump(dp,dict(status='UNTRUSTED_GENERATED_INPUTS',table=desc(table),segments=segments,checkpoints=data,dual_sparse_zipper_states_heads_agree_every_step=True,complete_support_agrees_at_each_checkpoint=True,final_whole_frame_metadata_match=final,proof_execution=False))
 inventory=dict(status='GENERATED_INPUTS_NOT_PROVED',unit_index=index,module=module,imports=imports,start=start,endpoint=at,segments=segments,checkpoint_name=prev_z,actual_run_theorem=prev_h,source=desc(sp),audit=desc(ap),data=desc(dp),generator=desc(Path(__file__).resolve()),canonical=desc(table),parents=parents,metadata_inputs=metadata_inputs,probes=names,callers=len(examples),proof_limits='default',intended_shared_source_audit_seconds=120,threads=1,memory_mib=4096,guard_emitted=False,proof_execution=False,final_target=END)
 dump(out/'source-inventory.json',inventory);print(json.dumps(inventory,indent=2))
if __name__=='__main__':main()
