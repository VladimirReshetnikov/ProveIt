import BusyBeaver.ZFC.Code254

/-!
Freshness of the actual four-tag decoder on every natural number.

For positive c, every bound or free label in dec c is smaller than c,
including labels introduced by nested zero codes. Code zero is different:
dec 0 = Rel(0,0) -> Rel(0,0), so label0 is syntactically free but its
satisfaction is independent of every valuation. The semantic support and
update lemmas therefore hold uniformly, including zero, without IR.

These statements concern the attributed original Code254 definitions.
They are not results for the different base3 or primitive-Bottom codecs.
They do not assert enc(dec c)=c, alter the bundle gates c != a,b, supply
native-equality GIC models or prove a numerical/machine calibration.
-/

namespace SetTheory.BusyBeaver.ZFC.DecodeFresh254

open Tarski (NF)

/-- The possible zero label also covers the decoder's exhausted-fuel case. -/
theorem occurs_decF_bound (fuel : Nat) : ∀ n i,
    NF.Occurs i (Code254.decF fuel n) → i < n ∨ i = 0 := by
  induction fuel with
  | zero =>
    intro n i h
    right
    simpa [Code254.decF, Code254.T0, NF.Occurs] using h
  | succ fuel ih =>
    intro n i h
    cases n with
    | zero =>
      right
      simpa [Code254.decF, Code254.T0, NF.Occurs] using h
    | succ n =>
      have hp := Code254.ofNat_le ((n + 1) / 4)
      have hd : (n + 1) / 4 < n + 1 := Nat.div_lt_self (by omega) (by omega)
      simp only [Code254.decF] at h
      split at h
      · simp only [NF.Occurs] at h
        rcases h with h | h
        · have hi := ih _ _ h
          left
          omega
        · have hi := ih _ _ h
          left
          omega
      · simp only [NF.Occurs] at h
        left
        rcases h with h | h <;> omega
      · simp only [NF.Occurs] at h
        left
        rcases h with h | h
        · omega
        · have hi := ih _ _ h
          omega
      · simp only [NF.Occurs] at h
        left
        rcases h with h | h <;> omega

/-- This quantifies over all positive codes, not just the named encoder image. -/
theorem occurs_lt_dec_pos (c i : Nat) (hc : 0 < c)
    (h : NF.Occurs i (Code254.dec c)) : i < c := by
  have hi := occurs_decF_bound (c + 1) c i h
  omega

theorem not_occurs_own_pos (c : Nat) (hc : 0 < c) :
    ¬ NF.Occurs c (Code254.dec c) := by
  intro h
  have := occurs_lt_dec_pos c c hc h
  omega

theorem not_free_own_pos (c : Nat) (hc : 0 < c) :
    ¬ NF.Free c (Code254.dec c) :=
  fun h => not_occurs_own_pos c hc (NF.Free.occurs h)

/-- A blanket syntactic-freshness statement at code zero would be false. -/
theorem free_zero : NF.Free 0 (Code254.dec 0) := by
  simp [Code254.dec_zero, Code254.T0, NF.Free]

universe u
variable {V : Type u}

/-- Only names strictly below c can affect satisfaction, even when c=0. -/
theorem sat_dec_ext (mem : V → V → Prop) (c : Nat) (e e' : Nat → V)
    (h : ∀ i, i < c → e i = e' i) :
    Tarski.Sat mem e (Code254.dec c) ↔ Tarski.Sat mem e' (Code254.dec c) := by
  cases c with
  | zero =>
    exact ⟨fun _ => Code254.sat_T0 mem e', fun _ => Code254.sat_T0 mem e⟩
  | succ c =>
    apply Tarski.sat_ext
    intro i hi
    exact h i (occurs_lt_dec_pos (c + 1) i (by omega) (NF.Free.occurs hi))

theorem sat_update_ge_code (mem : V → V → Prop) (c k : Nat) (hck : c ≤ k)
    (e : Nat → V) (x : V) :
    Tarski.Sat mem (Tarski.update e k x) (Code254.dec c) ↔
      Tarski.Sat mem e (Code254.dec c) := by
  apply sat_dec_ext
  intro i hi
  have hne : i ≠ k := by omega
  simp [Tarski.update, hne]

/-- Updating the matrix's own code label is harmless, including truth code0. -/
theorem sat_update_own_code (mem : V → V → Prop) (c : Nat)
    (e : Nat → V) (x : V) :
    Tarski.Sat mem (Tarski.update e c x) (Code254.dec c) ↔
      Tarski.Sat mem e (Code254.dec c) :=
  sat_update_ge_code mem c c (Nat.le_refl c) e x

/-- The auxiliary update can be ignored even beneath arbitrary input/output
updates. This is not permission to remove the original bundle gates. -/
theorem sat_context_update_own_code (mem : V → V → Prop) (c a b : Nat)
    (e : Nat → V) (v x y : V) :
    Tarski.Sat mem
      (Tarski.update (Tarski.update (Tarski.update e c v) a x) b y) (Code254.dec c) ↔
      Tarski.Sat mem (Tarski.update (Tarski.update e a x) b y) (Code254.dec c) := by
  apply sat_dec_ext
  intro i hi
  have hne : i ≠ c := by omega
  simp [Tarski.update, hne]

/-- These positive codes contain a zero child and need not lie in enc's image. -/
theorem dec_four : Code254.dec 4 = .imp (.rel 0 0) Code254.T0 := by decide

theorem dec_eight : Code254.dec 8 = .imp Code254.T0 (.rel 0 0) := by decide

end SetTheory.BusyBeaver.ZFC.DecodeFresh254
