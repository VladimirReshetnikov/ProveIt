import BusyBeaver.ZFC.KHomeReady

/-!
UNCOMPILED PROPOSAL for revision cbf94cb552a3b49509e0eee80e7455d4eb5974c6.
The only new proof is composition of two existing exec_sound instances.
No new symbolic step rule, register lemma, or branch-noninterference proof.
-/
namespace SetTheory.BusyBeaver.ZFC.KOracleCut
open KZip KRuntimeCore

def decCut (r : Nat) : SConf → Bool
  | (0, false, _, [.box (.mark r')]) => r == r'
  | _ => false

def runFrom (M : TMN) (fuel : Nat) (br : Branch) (s e : SConf) : Bool :=
  (KHomeReady.exec M br (fun t => sMatches t e) fuel s true).isSome

def forkTo (M : TMN) (fuel r : Nat) (s e0 ep : SConf) : Bool :=
  match KHomeReady.exec M none (decCut r) fuel s false with
  | none => false
  | some c => runFrom M fuel (some (r, true)) c e0 &&
      runFrom M fuel (some (r, false)) c ep

/-- Generic cut composition. Positive progress is supplied by the prefix;
the continuation may be reflexive. The cut's predicate can be arbitrary. -/
theorem execCut_sound {M : TMN} (B : BoxLemmas M)
    {cut tgt : SConf → Bool} {br : Branch} {f g : Nat} {s c t : SConf}
    (hp : KHomeReady.exec M none cut f s false = some c)
    (ht : KHomeReady.exec M br tgt g c true = some t)
    (n : Nat) {vs : List Nat} (hv : Valid br vs) :
    tgt t = true ∧ Reach1 M (conc n vs s) (conc n vs t) := by
  have vn : Valid none vs := ⟨hv.1, trivial⟩
  obtain ⟨_, _, hpos⟩ := KHomeReady.exec_sound B n vn f s false c hp
  obtain ⟨hmatch, hreach, _⟩ := KHomeReady.exec_sound B n hv g c true t ht
  exact ⟨hmatch, (hpos rfl).trans_reach hreach⟩

theorem forkTo_sound {M : TMN} (B : BoxLemmas M)
    {fuel r : Nat} {s e0 ep : SConf} (h : forkTo M fuel r s e0 ep = true)
    (z : Bool) (n : Nat) {vs : List Nat} (hv : Valid (some (r,z)) vs) :
    Reach1 M (conc n vs s) (conc n vs (if z then e0 else ep)) := by
  unfold forkTo at h
  cases hp : KHomeReady.exec M none (decCut r) fuel s false with
  | none => simp [hp] at h
  | some c =>
      have both : runFrom M fuel (some (r,true)) c e0 = true ∧
          runFrom M fuel (some (r,false)) c ep = true := by
        simpa only [hp, Bool.and_eq_true] using h
      have hs : runFrom M fuel (some (r,z)) c (if z then e0 else ep) = true := by
        cases z
        · exact both.2
        · exact both.1
      unfold runFrom at hs
      cases ht : KHomeReady.exec M (some (r,z))
          (fun t => sMatches t (if z then e0 else ep)) fuel c true with
      | none => simp [ht] at hs
      | some t =>
          obtain ⟨hm, hr⟩ := execCut_sound B hp ht n hv
          rw [← sMatches_conc n vs hm]
          exact hr

end SetTheory.BusyBeaver.ZFC.KOracleCut
