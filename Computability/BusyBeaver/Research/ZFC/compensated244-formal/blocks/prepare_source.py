from pathlib import Path
import json,hashlib
H=Path(__file__).parent;I=Path('/tmp/zfc244-248bc05936-inspection/zfc244-compensated-routing-20261018');D=json.loads((I/'runtime/contextual_fold_proof.json').read_text())
bo=lambda b:'true'if b else'false'
pos=lambda k:'h'if k==0 else f'(h + {k})'if k>0 else f'(h - {-k})'
hn=lambda k:'h0'if k==0 else f'hp{k}'if k>0 else f'hm{-k}'
# Consume fixed finite proof descriptors as untrusted statements to be checked in Lean.
# No table or tape transition is run by this emitter.
s='''import BusyBeaver.ZFC.TableCompensated244

/-!
Seven literal positive-block identities on arbitrary Core finite-support tapes.
All unspecified tape cells and the exact list representation are retained.
Each lemma states explicit read premises; the original245 invariant supplies
those premises for the167 and81 entries. No global simulation is asserted here.
-/
namespace SetTheory.BusyBeaver.ZFC.Compensated244Blocks

def cfgOld (q : Nat) (h : Int) (t : Tape) : Config 245 :=
  ⟨some (oldStateRouting245 q), h, t⟩
def cfgNew (q : Nat) (h : Int) (t : Tape) : Config 244 :=
  ⟨some (oldStateCompensated244 q), h, t⟩

private theorem step_read {n : Nat} (M : Machine n) (q q' : Fin n)
    (move : Move) (b : Bool) (h : Int) (t : Tape)
    (hb : Tape.read t h = b) (hr : M.transition q b = ⟨b, move, some q'⟩) :
    M.step ⟨some q, h, t⟩ = ⟨some q', move.apply h, t⟩ := by
  simp only [Machine.step, hb, hr]
  rw [← hb, Tape.write_read_self]

private theorem step_write {n : Nat} (M : Machine n) (q q' : Fin n)
    (move : Move) (b w : Bool) (h : Int) (t : Tape)
    (hb : Tape.read t h = b) (hr : M.transition q b = ⟨w, move, some q'⟩) :
    M.step ⟨some q, h, t⟩ = ⟨some q', move.apply h, Tape.write t h w⟩ := by
  simp only [Machine.step, hb, hr]
'''
a='import BusyBeaver.ZFC.Compensated244Blocks\n\nopen SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC\nopen SetTheory.BusyBeaver.ZFC.Compensated244Blocks\n\n';pub=[]
for case in D['macro_families']:
 name=case['name'];start=case['start'];window={int(k):v for k,v in case['known_input_cells'].items()};prem='\n'.join(f'    ({hn(k)} : Tape.read t {pos(k)} = {bo(v)})'for k,v in sorted(window.items()))
 ends={}
 for side,space,cfg in [('old','Routing245','cfgOld'),('new','Compensated244','cfgNew')]:
  traces=case[side+'_trace'];assert len(traces)==case[side+'_steps'];txt=f'\nprivate theorem {name}_{side} (h : Int) (t : Tape)\n{prem} :\n'
  tape='t';writes=[];steps=[]
  for j,tr in enumerate(traces,1):
   q=tr['state'];offset=tr['head'];b=tr['read'];w,d,target=tr['row'];nexth=offset+d;move='.right'if d==1 else'.left'
   assert offset in window and b==window[offset],(name,side,j) # Every cleared cell is left before any subsequent read.
   readproof=hn(offset)
   if writes:
    lines=[f'  have r{j} : Tape.read {tape} {pos(offset)} = {bo(b)} := by']
    for prior_t,wp,wb in reversed(writes):
     assert wp!=offset
     lines.append(f'    rw [Tape.read_write_of_ne {prior_t} (by omega : {pos(offset)} ≠ {pos(wp)}) {bo(wb)}]')
    lines.append(f'    exact {hn(offset)}');steps.extend(lines);readproof=f'r{j}'
   nextt=tape if w==b else f'(Tape.write {tape} {pos(offset)} {bo(w)})'
   steps.append(f'  have s{j} : machine{space}.step ({cfg} {q} {pos(offset)} {tape}) =\n      {cfg} {target} {pos(nexth)} {nextt} := by')
   arith=f'{pos(offset)} '+('+'if d==1 else'-')+' 1'
   headlemma=f'(show {arith} = {pos(nexth)} by omega)'
   method='step_read'if w==b else'step_write';bits=bo(b) if w==b else bo(b)+' '+bo(w)
   steps.append(f'    simpa only [{cfg}, Move.apply, {headlemma}] using\n      ({method} machine{space} (oldState{space} {q})\n        (oldState{space} {target}) {move} {bits} {pos(offset)} {tape}\n        {readproof} foldRow{space}_old{q}_{bo(b)})')
   if w!=b:writes.append((tape,offset,w))
   tape=nextt
  assert target==case['end_state']and nexth==case['end_head']
  ends[side]=(target,nexth,tape)
  txt+=f'    machine{space}.runFrom ({cfg} {start} h t) {len(traces)} =\n      {cfg} {target} {pos(nexth)} {tape} := by\n'+'\n'.join(steps)+'\n  simp only [Machine.runFrom]\n  rw ['+', '.join('s'+str(j)for j in range(1,len(traces)+1))+']\n'
  s+=txt
 assert ends['old']==ends['new'],name
 args=' '.join(hn(k)for k in sorted(window));pub.append(name)
 s+=f'\ntheorem {name} (h : Int) (t : Tape)\n{prem} :\n    embedConfig244 (machineCompensated244.runFrom (cfgNew {start} h t) {case["new_steps"]}) =\n      machineRouting245.runFrom (cfgOld {start} h t) {case["old_steps"]} := by\n  rw [{name}_new h t {args}, {name}_old h t {args}]\n  simp only [cfgNew, cfgOld, embedConfig244, Option.map_some, embedState244_old{target}]\n'
 a+=f'#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Blocks.{name}\n'
 a+=f'example (h : Int) (t : Tape)\n{prem} :\n    embedConfig244 (machineCompensated244.runFrom (cfgNew {start} h t) {case["new_steps"]}) =\n      machineRouting245.runFrom (cfgOld {start} h t) {case["old_steps"]} :=\n  {name} h t {args}\n\n'
s+='\nend SetTheory.BusyBeaver.ZFC.Compensated244Blocks\n';(H/'Compensated244Blocks.lean').write_text(s);(H/'Audit.lean').write_text(a)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
o=dict(status='SOURCE_ONLY',source=dict(path=str(H/'Compensated244Blocks.lean'),sha256=sha(H/'Compensated244Blocks.lean')),audit=dict(path=str(H/'Audit.lean'),sha256=sha(H/'Audit.lean')),untrusted_descriptor=dict(path=str(I/'runtime/contextual_fold_proof.json'),sha256=sha(I/'runtime/contextual_fold_proof.json')),generator=dict(path=str(Path(__file__).resolve()),sha256=sha(__file__)),probes=7,callers=7,claims=pub,scope='Pure proof-source emitter; supplied code/simulator/guard/compiler never invoked. Untrusted traces appear only as proposed Lean statements, independently checked literal table row lemmas and explicit read hypotheses.')
(H/'source-inventory.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o))
