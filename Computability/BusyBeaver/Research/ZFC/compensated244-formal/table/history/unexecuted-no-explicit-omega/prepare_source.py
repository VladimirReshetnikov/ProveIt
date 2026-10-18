from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');I=Path('/tmp/zfc244-248bc05936-inspection/zfc244-compensated-routing-20261018');O=Path(__file__).parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def table(p):
 rows={}
 for l in p.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,t=l.split();key=(int(q),int(b));assert key not in rows;rows[key]=(int(w),d,int(t))
 return rows
C=I/'machine/zfc_compensated244.tm';L=I/'machine/zfc_compensated244_old.tm';J=I/'machine/renumbering.json'
labels=json.loads(J.read_text())['canonical_to_old'];assert len(labels)==244 and len(set(labels))==244 and labels[0]==95 and 122 not in labels
oldmap={int(k):v for k,v in json.loads(J.read_text())['old_to_canonical'].items()};assert oldmap[254]==244
new=table(C);old=table(L);assert len(new)==len(old)==488
for q,l in enumerate(labels):
 for b in [0,1]:
  w,d,t=old[l,b];assert new[q,b]==(w,d,oldmap[t])
B=R/'Computability/BusyBeaver/Research/ZFC/candidate-routing245/zfc_routing245_old.tm';old245=table(B)
assert len(old245)==490 and set(old)==set(old245)-{(122,0),(122,1)}
delta={k:(old245[k],old[k])for k in old if old245[k]!=old[k]}
assert delta=={(92,1):((1,'L',24),(1,'R',66)),(104,1):((1,'R',122),(1,'R',92)),(106,1):((1,'R',122),(1,'R',92)),(167,1):((1,'L',92),(1,'L',151))}
# Pure syntax/data emission; no transition execution or imported delivered code.
bo=lambda b:'true'if b else'false';mv=lambda d:'.left'if d=='L'else'.right'
raw=lambda a:f'({bo(a[0])}, {mv(a[1])}, {a[2]})'
s='''import BusyBeaver.ZFC.TableRouting245

/-!
Exact compensated244 canonical table and its embedding into the retained245
state labels. The finite table deletes old122 and changes exactly four rows.
The original245 table remains the checked reference. This module states only
literal table, renumbering, and common-transition facts; no runtime theorem.
Core configurations carry arbitrary finite-support List Int tapes.
-/
namespace SetTheory.BusyBeaver.ZFC

abbrev RawActionCompensated244 := Bool × Move × Nat

def rawTableCompensated244 : Array (RawActionCompensated244 × RawActionCompensated244) := #[
'''
s+='\n'.join(f'  ({raw(new[q,0])}, {raw(new[q,1])})'+(','if q<243 else'')+f' -- {q}; old{l}'for q,l in enumerate(labels))+'\n]\n'
s+='''
theorem rawTableCompensated244_size : rawTableCompensated244.size = 244 := by decide +kernel

theorem rawTableCompensated244_transition_count :
    (rawTableCompensated244.toList.flatMap (fun r => [r.1, r.2])).length = 488 := by
  decide +kernel

def rawActionCompensated244 (q : Fin 244) (b : Bool) : RawActionCompensated244 :=
  let row := rawTableCompensated244.getD q.val
    ((false, .right, 244), (false, .right, 244))
  if b then row.2 else row.1

def actionCompensated244 (q : Fin 244) (b : Bool) : Action 244 :=
  let raw := rawActionCompensated244 q b
  { write := raw.1, move := raw.2.1,
    next := if h : raw.2.2 < 244 then some ⟨raw.2.2, h⟩ else none }

def machineCompensated244 : Machine 244 where
  transition := actionCompensated244

/-- Original labels; absent labels have only a total fallback value. -/
def oldStateCompensated244 : Nat → Fin 244
'''
s+='\n'.join(f'  | {l} => {q}'for q,l in enumerate(labels))+'\n  | _ => 0\n'
s+='''
/-- The sole deleted old state is canonical113 in Routing245. -/
def embedState244 (q : Fin 244) : Fin 245 :=
  if h : q.val < 113 then ⟨q.val, by omega⟩ else ⟨q.val + 1, by omega⟩

def embedAction244 (a : Action 244) : Action 245 :=
  ⟨a.write, a.move, a.next.map embedState244⟩

def embedConfig244 (c : Config 244) : Config 245 :=
  ⟨c.state.map embedState244, c.head, c.tape⟩

theorem embedState244_ne_deleted : ∀ q,
    embedState244 q ≠ oldStateRouting245 122 := by decide +kernel

theorem embedState244_zero : embedState244 0 = 0 := by decide +kernel

theorem embedConfig244_initial : embedConfig244 (initial 244) = initial 245 := by
  rfl

/-- Four entry rows use the separately proved positive blocks. -/
def exceptionalRow244 (q : Fin 244) (b : Bool) : Prop :=
  b = true ∧ (q = oldStateCompensated244 104 ∨ q = oldStateCompensated244 106 ∨
    q = oldStateCompensated244 167 ∨ q = oldStateCompensated244 81)

instance (q : Fin 244) (b : Bool) : Decidable (exceptionalRow244 q b) :=
  inferInstanceAs (Decidable (b = true ∧ (q = oldStateCompensated244 104 ∨
    q = oldStateCompensated244 106 ∨ q = oldStateCompensated244 167 ∨
    q = oldStateCompensated244 81)))

/-- All482 ordinary retained rows agree, including final write/move on halt. -/
theorem compensated244_common_action : ∀ (q : Fin 244) (b : Bool),
    q ≠ oldStateCompensated244 92 → ¬ exceptionalRow244 q b →
      embedAction244 (machineCompensated244.transition q b) =
        machineRouting245.transition (embedState244 q) b := by decide +kernel

theorem compensated244_common_next : ∀ (q : Fin 244) (b : Bool),
    q ≠ oldStateCompensated244 92 → ¬ exceptionalRow244 q b →
      (machineCompensated244.transition q b).next ≠
        some (oldStateCompensated244 92) := by decide +kernel
'''
# Every literal row needed by seven local identities, plus endpoints/start.
keys={(104,1),(106,1),(122,0),(122,1),(92,0),(92,1),(107,1),(125,0),(167,1),(151,1),(81,1),(24,1),(37,1),(55,1),(66,1),(20,1)}
names=[]
for n,tab,typ in [('Routing245',old245,245),('Compensated244',old,244)]:
 for q,b in sorted(keys):
  if(q,b)not in tab:continue
  w,d,t=tab[q,b];name=f'foldRow{n}_old{q}_{bo(b)}';names.append(name)
  s+=f'\ntheorem {name} :\n    machine{n}.transition (oldState{n} {q}) {bo(b)} =\n      ⟨{bo(w)}, {mv(d)}, some (oldState{n} {t})⟩ := by decide +kernel\n'
embedlabels=sorted({2,20,24,25,37,55,66,81,92,95,104,106,107,125,151,167})
for q in embedlabels:
 name=f'embedState244_old{q}';names.append(name)
 s+=f'\ntheorem {name} :\n    embedState244 (oldStateCompensated244 {q}) = oldStateRouting245 {q} := by decide +kernel\n'
s+='\nend SetTheory.BusyBeaver.ZFC\n';(O/'TableCompensated244.lean').write_text(s)
probes=['rawTableCompensated244_size','rawTableCompensated244_transition_count','embedState244_ne_deleted','embedState244_zero','embedConfig244_initial','compensated244_common_action','compensated244_common_next']+names
# Every public finite fact is probed; typed clients cover data, all-row relation, embedding.
a='import BusyBeaver.ZFC.TableCompensated244\n\nopen SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC\n\n'+'\n'.join('#print axioms SetTheory.BusyBeaver.ZFC.'+n for n in probes)+'\n\n'
a+='''example : Machine 244 := machineCompensated244
example : rawTableCompensated244.size = 244 := rawTableCompensated244_size
example (q : Fin 244) : embedState244 q ≠ oldStateRouting245 122 := embedState244_ne_deleted q
example : embedConfig244 (initial 244) = initial 245 := embedConfig244_initial
example (q : Fin 244) (b : Bool) (h : q ≠ oldStateCompensated244 92)
    (he : ¬ exceptionalRow244 q b) :
    embedAction244 (machineCompensated244.transition q b) = machineRouting245.transition (embedState244 q) b :=
  compensated244_common_action q b h he
example (q : Fin 244) (b : Bool) (h : q ≠ oldStateCompensated244 92)
    (he : ¬ exceptionalRow244 q b) :
    (machineCompensated244.transition q b).next ≠ some (oldStateCompensated244 92) :=
  compensated244_common_next q b h he
'''
(O/'Audit.lean').write_text(a)
out=dict(status='SOURCE_ONLY',source=dict(path=str(O/'TableCompensated244.lean'),sha256=sha(O/'TableCompensated244.lean')),audit=dict(path=str(O/'Audit.lean'),sha256=sha(O/'Audit.lean')),inputs=[dict(path=str(p),sha256=sha(p))for p in [C,L,J,B]],working_states=244,rows=488,deleted_old_state=122,deleted_old_canonical=113,patch=[dict(state=q,read=b,old=left,new=right)for(q,b),(left,right)in delta.items()],probes=len(probes),callers=6,generator=dict(path=str(Path(__file__).resolve()),sha256=sha(__file__)),execution='Own pure parser/emitter only; no supplied program/simulator/guard/compiler.')
(O/'source-inventory.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
