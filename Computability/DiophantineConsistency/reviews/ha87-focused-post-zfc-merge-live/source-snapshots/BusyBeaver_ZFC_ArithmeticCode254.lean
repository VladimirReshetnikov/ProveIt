import BusyBeaver.ZFC.ArithmeticCantor

/-!
Explicit fixed bounded graphs for the live base4 numerical constructors and
one axiom row. These are arbitrary-IOpen arithmetic components, not a represented
complete checker/history or an internal PA machine theorem.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticCode254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

/-- A polynomial input bound, in the unextended ring language. -/
theorem cantor_polybound (a b : V) :
    cantor a b ≤ (a + b) * (a + b + 1) + b := by
  have ht : triangle (a + b) ≤ (a + b) * (a + b + 1) := by
    have h := mul_le_mul_of_nonneg_right (show (1 : V) ≤ 2 by simp)
      (Arithmetic.zero_le (triangle (a + b)))
    simpa only [one_mul, triangle_double] using h
  exact _root_.add_le_add ht le_rfl

instance cantor_bounded : Bounded₂ (cantor : V → V → V) :=
  ⟨‘a b. (a + b) * (a + b + 1) + b’, fun v => by
    simpa using cantor_polybound (v 0) (v 1)⟩

noncomputable def tagged (k a b : V) : V := 4 * cantor a b + k
noncomputable def wim (a b : V) : V := tagged 0 a b
noncomputable def wel (a b : V) : V := tagged 1 a b
noncomputable def wal (a b : V) : V := tagged 2 a b
noncomputable def weq (a b : V) : V := tagged 3 a b

lemma pair_le_tagged (k a b : V) : cantor a b ≤ tagged k a b := by
  have hm := mul_le_mul_of_nonneg_right (show (1 : V) ≤ 4 by simp)
    (Arithmetic.zero_le (cantor a b))
  exact le_trans (by simpa only [one_mul] using hm) (by simp [tagged])

lemma tagged_components (k a b : V) : a ≤ tagged k a b ∧ b ≤ tagged k a b :=
  ⟨le_trans (components_le a b).1 (pair_le_tagged k a b),
   le_trans (components_le a b).2 (pair_le_tagged k a b)⟩

instance tagged_bounded : Bounded₃ (tagged : V → V → V → V) :=
  ⟨‘k a b. 4 * ((a + b) * (a + b + 1) + b) + k’, fun v => by
    simpa [tagged] using (_root_.add_le_add
      (mul_le_mul_of_nonneg_left (cantor_polybound (v 1) (v 2)) (show (0 : V) ≤ 4 by simp))
      (le_refl (v 0)))⟩

/-- The tag is an arithmetic input. Every existential is output-bounded. -/
def taggedDef : 𝚺₀.Semisentence 4 := .mkSigma
  “r k a b. ∃ p <⁺ r, !ArithmeticCantor.pairDef p a b ∧ r = 4 * p + k”

instance tagged_defined : 𝚺₀-Function₃[V] tagged via taggedDef := .mk fun v => by
  simp [taggedDef]
  constructor
  · intro h; exact h.2
  · intro hr
    exact ⟨by rw [hr]; exact pair_le_tagged _ _ _, hr⟩

def wimDef : 𝚺₀.Semisentence 3 := .mkSigma “r a b. !taggedDef r 0 a b”
def welDef : 𝚺₀.Semisentence 3 := .mkSigma “r a b. !taggedDef r 1 a b”
def walDef : 𝚺₀.Semisentence 3 := .mkSigma “r a b. !taggedDef r 2 a b”
def weqDef : 𝚺₀.Semisentence 3 := .mkSigma “r a b. !taggedDef r 3 a b”

instance wim_defined : 𝚺₀-Function₂[V] wim via wimDef := .mk fun v => by simp [wimDef, wim]
instance wel_defined : 𝚺₀-Function₂[V] wel via welDef := .mk fun v => by simp [welDef, wel]
instance wal_defined : 𝚺₀-Function₂[V] wal via walDef := .mk fun v => by simp [walDef, wal]
instance weq_defined : 𝚺₀-Function₂[V] weq via weqDef := .mk fun v => by simp [weqDef, weq]

@[simp] theorem tagged_nat (k a b : Nat) : tagged k a b = 4 * Code254.P a b + k := by
  unfold tagged
  rw [← numeral_four_eq_four]
  simp only [cantor_nat, Nat.numeral_eq]

@[simp] theorem wim_nat (a b : Nat) : wim a b = Code254.wim a b := by
  simp only [wim, tagged_nat, Code254.wim, add_zero]
@[simp] theorem wel_nat (a b : Nat) : wel a b = Code254.wel a b := by
  simp only [wel, tagged_nat, Code254.wel]
@[simp] theorem wal_nat (a b : Nat) : wal a b = Code254.wal a b := by
  unfold wal
  rw [← numeral_two_eq_two]
  simp only [tagged_nat, Nat.numeral_eq, Code254.wal]
@[simp] theorem weq_nat (a b : Nat) : weq a b = Code254.weq a b := by
  unfold weq
  rw [← numeral_three_eq_three]
  simp only [tagged_nat, Nat.numeral_eq, Code254.weq]

/-! A whole axiom circuit: rho1(a,b) = ¬∀a¬Eq(a,b), using relative F=1.
All three auxiliary constructor outputs are bounded by the final output. -/
noncomputable def rho1 (a b : V) : V := wim (wal a (wim (weq a b) 1)) 1

def rho1Def : 𝚺₀.Semisentence 3 := .mkSigma
  “r a b. ∃ e <⁺ r, !weqDef e a b ∧
    ∃ n <⁺ r, !wimDef n e 1 ∧
    ∃ q <⁺ r, !walDef q a n ∧ !wimDef r q 1”

instance rho1_defined : 𝚺₀-Function₂[V] rho1 via rho1Def := .mk fun v => by
  simp [rho1Def]
  constructor
  · intro h; exact h.2.2.2
  · intro hr
    have hq : wal (v 1) (wim (weq (v 1) (v 2)) 1) ≤ rho1 (v 1) (v 2) :=
      (tagged_components 0 _ _).1
    have hn : wim (weq (v 1) (v 2)) 1 ≤ rho1 (v 1) (v 2) :=
      le_trans (tagged_components 2 _ _).2 hq
    have he : weq (v 1) (v 2) ≤ rho1 (v 1) (v 2) :=
      le_trans (tagged_components 0 _ _).1 hn
    exact ⟨by simpa only [hr] using he, by simpa only [hr] using hn,
      by simpa only [hr] using hq, hr⟩

@[simp] theorem rho1_nat (a b : Nat) : rho1 a b = Code254.rho1 a b := by
  simp only [rho1, wim_nat, wal_nat, weq_nat, Code254.rho1,
    Code254.wex, Code254.wn, Code254.F]

/-- Value returned by the proof-checker's unconditional rho1/tag3 branch.
This is a graph of that fixed branch only, not the whole12-case evaluator. -/
noncomputable def rho1Value (a b : V) : V := rho1 a b + 1

def rho1ValueDef : 𝚺₀.Semisentence 3 := .mkSigma
  “v a b. ∃ r <⁺ v, !rho1Def r a b ∧ v = r + 1”

instance rho1Value_defined : 𝚺₀-Function₂[V] rho1Value via rho1ValueDef := .mk fun v => by
  simp [rho1ValueDef]
  constructor
  · intro h; exact h.2
  · intro hv
    exact ⟨by rw [hv]; simp [rho1Value], hv⟩

@[simp] theorem rho1Value_nat (a b : Nat) : rho1Value a b = Code254.rho1 a b + 1 := by
  simp only [rho1Value, rho1_nat]

/-! Literal Cantor payload adapter for the unconditional tag3 branch. -/

lemma rho1_input_bounds (a b : V) : a ≤ rho1 a b ∧ b ≤ rho1 a b := by
  have hq : wal a (wim (weq a b) 1) ≤ rho1 a b := (tagged_components 0 _ _).1
  have hn : wim (weq a b) 1 ≤ rho1 a b := le_trans (tagged_components 2 _ _).2 hq
  have he : weq a b ≤ rho1 a b := le_trans (tagged_components 0 _ _).1 hn
  exact ⟨le_trans (tagged_components 3 _ _).1 he,
    le_trans (tagged_components 3 _ _).2 he⟩

noncomputable def row3 (payload : V) : V := rho1Value (first payload) (second payload)

def row3Def : 𝚺₀.Semisentence 2 := .mkSigma
  “v p. ∃ a <⁺ v, ∃ b <⁺ v,
    !ArithmeticCantor.pairDef p a b ∧ !rho1ValueDef v a b”

instance row3_defined : 𝚺₀-Function₁[V] row3 via row3Def := .mk fun v => by
  simp [row3Def]
  constructor
  · rintro ⟨a, _, b, _, hp, hv⟩
    simpa only [row3, hp, first_cantor, second_cantor] using hv
  · intro hv
    have hb := rho1_input_bounds (first (v 1)) (second (v 1))
    have hr : rho1 (first (v 1)) (second (v 1)) ≤ row3 (v 1) := by simp [row3, rho1Value]
    exact ⟨first (v 1), by rw [hv]; exact le_trans hb.1 hr,
      second (v 1), by rw [hv]; exact le_trans hb.2 hr,
      (projections_spec (v 1)).2.2, hv⟩

@[simp] theorem row3_nat (p : Nat) : row3 p =
    Code254.rho1 (SetTheory.Cantor.ofNat p).1 (SetTheory.Cantor.ofNat p).2 + 1 := by
  simp only [row3, rho1Value_nat, first_nat, second_nat]

/-! The same fixed graphs, directly packaged for the live standard-Nat code. -/
instance codeWim_defined :
    HierarchySymbol.DefinedFunction₂ (V := Nat) 𝚺₀ Code254.wim wimDef := by
  have he : (wim : Nat → Nat → Nat) = Code254.wim := funext fun a => funext fun b => wim_nat a b
  rw [← he]; exact wim_defined
instance codeWel_defined :
    HierarchySymbol.DefinedFunction₂ (V := Nat) 𝚺₀ Code254.wel welDef := by
  have he : (wel : Nat → Nat → Nat) = Code254.wel := funext fun a => funext fun b => wel_nat a b
  rw [← he]; exact wel_defined
instance codeWal_defined :
    HierarchySymbol.DefinedFunction₂ (V := Nat) 𝚺₀ Code254.wal walDef := by
  have he : (wal : Nat → Nat → Nat) = Code254.wal := funext fun a => funext fun b => wal_nat a b
  rw [← he]; exact wal_defined
instance codeWeq_defined :
    HierarchySymbol.DefinedFunction₂ (V := Nat) 𝚺₀ Code254.weq weqDef := by
  have he : (weq : Nat → Nat → Nat) = Code254.weq := funext fun a => funext fun b => weq_nat a b
  rw [← he]; exact weq_defined
instance codeRho1_defined :
    HierarchySymbol.DefinedFunction₂ (V := Nat) 𝚺₀ Code254.rho1 rho1Def := by
  have he : (rho1 : Nat → Nat → Nat) = Code254.rho1 := funext fun a => funext fun b => rho1_nat a b
  rw [← he]; exact rho1_defined
instance codeRho1Value_defined :
    HierarchySymbol.DefinedFunction₂ (V := Nat) 𝚺₀ (fun a b => Code254.rho1 a b + 1) rho1ValueDef := by
  have he : (rho1Value : Nat → Nat → Nat) = fun a b => Code254.rho1 a b + 1 :=
    funext fun a => funext fun b => rho1Value_nat a b
  rw [← he]; exact rho1Value_defined
instance codeRow3_defined :
    HierarchySymbol.DefinedFunction₁ (V := Nat) 𝚺₀
      (fun p => Code254.rho1 (SetTheory.Cantor.ofNat p).1 (SetTheory.Cantor.ofNat p).2 + 1) row3Def := by
  have he : (row3 : Nat → Nat) =
      fun p => Code254.rho1 (SetTheory.Cantor.ofNat p).1 (SetTheory.Cantor.ofNat p).2 + 1 := funext row3_nat
  rw [← he]; exact row3_defined

end SetTheory.BusyBeaver.ZFC.ArithmeticCode254
