import BusyBeaver.ZFC.Code254Proof
import BusyBeaver.ZFC.KCode222

set_option autoImplicit false
set_option Elab.async false

/-! An actual Nat checker for C222. Only the raw tree datatype, quoting and
fuel-bounded parser are reused from Code254Proof. Conclusions and recursive
MP validity are defined anew; no old semantic soundness theorem is used. -/
namespace SetTheory.BusyBeaver.ZFC.Code222Proof

open Code254
open Code254Proof (RawProof decodeFuel)
open KCode222 (C222)

/-- The syntactic `.r7` node now denotes the actual merged equality row. -/
def conclusion222 : RawProof → Nat
  | .truth => 0
  | .mp b _ _ => b
  | .gen a p => wal a (conclusion222 p)
  | .r1 a b => rho1 a b
  | .r2 a b c => rho2 a b c
  | .r3 a b c => rho3 a b c
  | .r4 a b c => rho4 a b c
  | .r5 a b c => rho5 a b c
  | .r6 a b => rho6 a b
  | .r7 a b c => KCode222.growG a b c
  | .r8 a b c u => rho8 a b c u
  | .bundle a b c => KCode222.bundle222 a b c

/-- Both MP subtrees and the comparison of their new conclusions are checked.
The actual bundle gate is just c!=a and c!=b. -/
def valid222 : RawProof → Bool
  | .truth => true
  | .mp b p q => valid222 p &&
      (valid222 q && decide (conclusion222 q = wim (conclusion222 p) b))
  | .gen _ p => valid222 p
  | .bundle a b c => decide (c ≠ a) && decide (c ≠ b)
  | _ => true

theorem sound (p : RawProof) : valid222 p = true → C222 (conclusion222 p) := by
  induction p with
  | truth => intro _; exact .truth
  | mp b p q ihp ihq =>
    intro h
    simp only [valid222, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .mp (ihp h.1) (h.2.2 ▸ ihq h.2.1)
  | gen a p ih => intro h; exact .gen a (ih h)
  | r1 a b => intro _; exact .r1 a b
  | r2 a b c => intro _; exact .r2 a b c
  | r3 a b c => intro _; exact .r3 a b c
  | r4 a b c => intro _; exact .r4 a b c
  | r5 a b c => intro _; exact .r5 a b c
  | r6 a b => intro _; exact .r6 a b
  | r7 a b c => intro _; exact .rG a b c
  | r8 a b c u => intro _; exact .r8 a b c u
  | bundle a b c =>
    intro h
    simp only [valid222, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .bundle a b c h.1 h.2

/-- Existence of finite data follows by induction on the actual C222
derivation; there is no inspection of a proof into a chosen computational tree. -/
theorem rawProof_exists {n : Nat} (h : C222 n) :
    ∃ p : RawProof, valid222 p = true ∧ conclusion222 p = n := by
  induction h with
  | truth => exact ⟨.truth, rfl, rfl⟩
  | @mp t b _ _ ihp ihq =>
    obtain ⟨p, hp, hpn⟩ := ihp
    obtain ⟨q, hq, hqn⟩ := ihq
    exact ⟨.mp b p q, by simp [valid222, hp, hq, hpn, hqn], rfl⟩
  | gen a _ ih =>
    obtain ⟨p, hp, hpn⟩ := ih
    exact ⟨.gen a p, hp, by simp only [conclusion222, hpn]⟩
  | r1 a b => exact ⟨.r1 a b, rfl, rfl⟩
  | r2 a b c => exact ⟨.r2 a b c, rfl, rfl⟩
  | r3 a b c => exact ⟨.r3 a b c, rfl, rfl⟩
  | r4 a b c => exact ⟨.r4 a b c, rfl, rfl⟩
  | r5 a b c => exact ⟨.r5 a b c, rfl, rfl⟩
  | r6 a b => exact ⟨.r6 a b, rfl, rfl⟩
  | rG a b c => exact ⟨.r7 a b c, rfl, rfl⟩
  | r8 a b c u => exact ⟨.r8 a b c u, rfl, rfl⟩
  | bundle a b c hca hcb =>
    exact ⟨.bundle a b c, by simp [valid222, hca, hcb], rfl⟩

/-- The unchanged parser is total on every Nat, including malformed codes.
Its fuel is code+1, exactly as in the original coding. -/
def check222 (code n : Nat) : Bool :=
  match decodeFuel (code + 1) code with
  | none => false
  | some p => valid222 p && decide (conclusion222 p = n)

theorem check_sound {code n : Nat} (h : check222 code n = true) : C222 n := by
  unfold check222 at h
  cases he : decodeFuel (code + 1) code with
  | none => simp [he] at h
  | some p =>
    simp only [he, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2 ▸ sound p h.1

theorem check_quote (p : RawProof) :
    check222 p.quote (conclusion222 p) = valid222 p := by
  unfold check222
  rw [p.decode_quote (p.quote + 1) (by have := p.height_le_quote; omega)]
  simp

/-- Exact external numerical coding of the actual C222 relation. This does
not yet represent this checker in an arithmetic theory or a machine runtime. -/
theorem c222_iff_checked (n : Nat) : C222 n ↔ ∃ code, check222 code n = true := by
  constructor
  · intro h
    obtain ⟨p, hp, hpn⟩ := rawProof_exists h
    exact ⟨p.quote, by rw [← hpn, check_quote]; exact hp⟩
  · rintro ⟨code, h⟩
    exact check_sound h

theorem reject_zero (n : Nat) : check222 0 n = false := rfl

theorem accept_truth : check222 1 0 = true := by decide

theorem accept_growG (a b c : Nat) :
    check222 (RawProof.r7 a b c).quote (KCode222.growG a b c) = true :=
  check_quote (.r7 a b c)

theorem accept_bundle (a b c : Nat) (hca : c ≠ a) (hcb : c ≠ b) :
    check222 (RawProof.bundle a b c).quote (KCode222.bundle222 a b c) = true := by
  have hv : valid222 (.bundle a b c) = true := by
    simp only [valid222, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hca, hcb⟩
  exact (check_quote (.bundle a b c)).trans hv

end SetTheory.BusyBeaver.ZFC.Code222Proof
