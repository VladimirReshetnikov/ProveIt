import BusyBeaver.ZFC.ArithmeticTemplates254
import BusyBeaver.ZFC.Code254History

/-!
Fixed bounded graphs for the complete rule row, with its two child results
supplied as explicit numeric inputs. The history lookup and outer proof-code
selector are separate. Failed MP and bundle gates return exactly zero; no
intermediate is bounded by that rejected output.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticRow254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

lemma pred_add_one (u : V) (hu : u ≠ 0) : u - 1 + 1 = u := by
  have hpos : 0 < u := lt_of_le_of_ne (Arithmetic.zero_le u) (Ne.symm hu)
  exact tsub_add_cancel_of_le (by simpa using lt_iff_succ_le.mp hpos)

lemma pred_le (u : V) : u - 1 ≤ u := tsub_le_self

/-- The MP test uses predecessor witnesses bounded by the two child results,
including when the proposed row result is zero. -/
def MPGate (a u v : V) : Prop :=
  ∃ x, x ≤ u ∧ ∃ m, m ≤ v ∧ u = x + 1 ∧ v = m + 1 ∧ m = wim x a

def mpGateDef : 𝚺₀.Semisentence 3 := .mkSigma
  “a u v. ∃ x <⁺ u, ∃ m <⁺ v,
    u = x + 1 ∧ v = m + 1 ∧ !wimDef m x a”

instance mpGate_defined : 𝚺₀-Relation₃[V] MPGate via mpGateDef :=
  .mk fun e => by simp [mpGateDef, MPGate]

noncomputable def mpValue (a u v : V) : V := by
  classical
  exact if MPGate a u v then a + 1 else 0

def mpDef : 𝚺₀.Semisentence 4 := .mkSigma
  “r a u v. (!mpGateDef a u v ∧ r = a + 1) ∨ (¬ !mpGateDef a u v ∧ r = 0)”

instance mp_defined : 𝚺₀-Function₃[V] mpValue via mpDef := .mk fun e => by
  classical
  by_cases h : MPGate (e 1) (e 2) (e 3) <;> simp [mpDef, mpValue, h]

@[simp] lemma bounded_succ_iff (z r : V) : (z ≤ r ∧ r = z + 1) ↔ r = z + 1 := by
  constructor
  · exact fun h => h.2
  · intro h
    rw [h]
    simp

lemma predecessor_witness (u : V) (Q : V → Prop) :
    (∃ x, x ≤ u ∧ u = x + 1 ∧ Q x) ↔ u ≠ 0 ∧ Q (u - 1) := by
  constructor
  · rintro ⟨x, _, h, hQ⟩
    have hne : u ≠ 0 := by rw [h]; simp
    have hp : u - 1 = x := by rw [h]; simp
    exact ⟨hne, hp ▸ hQ⟩
  · rintro ⟨hu, hQ⟩
    exact ⟨u - 1, pred_le u, (pred_add_one u hu).symm, hQ⟩

noncomputable def genValue (a u : V) : V := by
  classical
  exact if u = 0 then 0 else wal a (u - 1) + 1

def genDef : 𝚺₀.Semisentence 3 := .mkSigma
  “r a u. (u = 0 ∧ r = 0) ∨
    (∃ x <⁺ u, u = x + 1 ∧ ∃ f <⁺ r, !walDef f a x ∧ r = f + 1)”

instance gen_defined : 𝚺₀-Function₂[V] genValue via genDef := .mk fun e => by
  classical
  simp [genDef]
  rw [predecessor_witness]
  by_cases h : e 2 = 0 <;> simp [genValue, h]

/-- Payload decompositions are bounded by the payload even for rejected rows. -/
lemma payload_fields (p : V) (Q : V → V → V → V → Prop) :
    (∃ a, a ≤ p ∧ ∃ t, t ≤ p ∧ p = cantor a t ∧
      ∃ b, b ≤ p ∧ ∃ c, c ≤ p ∧ t = cantor b c ∧ Q a t b c) ↔
    Q (first p) (second p) (first (second p)) (second (second p)) := by
  constructor
  · rintro ⟨a, _, t, _, hp, b, _, c, _, ht, hQ⟩
    subst p
    simp only [first_cantor, second_cantor]
    rw [ht, first_cantor, second_cantor]
    simpa only [ht] using hQ
  · intro hQ
    have hp := projections_spec p
    have ht := projections_spec (second p)
    exact ⟨first p, hp.1, second p, hp.2.1, hp.2.2,
      first (second p), le_trans ht.1 hp.2.1,
      second (second p), le_trans ht.2.1 hp.2.1, ht.2.2, hQ⟩



@[simp] theorem foundation_sub_nat (a b : Nat) : Arithmetic.sub a b = a - b := by
  symm
  apply (Arithmetic.sub_existsUnique a b).unique
  · constructor
    · intro h
      have h' : b = a ∨ b < a := Arithmetic.le_def.mp h
      clear h
      omega
    · intro h
      omega
  · exact Classical.choose!_spec (Arithmetic.sub_existsUnique a b)

@[simp] theorem mpGate_nat (a u v : Nat) :
    MPGate a u v ↔ u ≠ 0 ∧ v ≠ 0 ∧ v - 1 = Code254.wim (u - 1) a := by
  constructor
  · rintro ⟨x, _, m, _, hu, hv, hm⟩
    simp [hu, hv, ← wim_nat, hm]
  · rintro ⟨hu, hv, hm⟩
    refine ⟨u - 1, ?_, v - 1, ?_, ?_, ?_, ?_⟩
    · rw [Arithmetic.le_def]; omega
    · rw [Arithmetic.le_def]; omega
    · omega
    · omega
    · simpa only [wim_nat] using hm

@[simp] theorem mpValue_nat (a u v : Nat) : mpValue a u v =
    (if u = 0 ∨ v = 0 then 0 else if v - 1 = Code254.wim (u - 1) a then a + 1 else 0) := by
  classical
  simp only [mpValue, mpGate_nat]
  by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> simp [hu, hv]

@[simp] theorem genValue_nat (a u : Nat) : genValue a u =
    (if u = 0 then 0 else Code254.wal a (u - 1) + 1) := by
  classical
  simp only [genValue, wal_nat]
  change (if u = 0 then 0 else Code254.wal a (Arithmetic.sub u 1) + 1) =
    (if u = 0 then 0 else Code254.wal a (u - 1) + 1)
  rw [foundation_sub_nat]

/-- Two components can be bounded by any bound on their paired payload. -/
lemma pair_fields (p bound : V) (hp : p ≤ bound) (Q : V → V → Prop) :
    (∃ a, a ≤ bound ∧ ∃ b, b ≤ bound ∧ p = cantor a b ∧ Q a b) ↔
      Q (first p) (second p) := by
  constructor
  · rintro ⟨a, _, b, _, h, hQ⟩
    subst p
    simpa only [first_cantor, second_cantor] using hQ
  · intro hQ
    have h := projections_spec p
    exact ⟨first p, le_trans h.1 hp, second p, le_trans h.2.1 hp, h.2.2, hQ⟩

noncomputable def rowKernel (k p u v : V) : V := by
  classical
  let a := first p
  let t := second p
  let b := first t
  let c := second t
  exact if k = 0 then (if p = 0 then 1 else 0)
    else if k = 1 then mpValue a u v
    else if k = 2 then genValue a u
    else if k = 3 then ArithmeticCode254.rho1 a t + 1
    else if k = 4 then ArithmeticTemplates254.rho2 a b c + 1
    else if k = 5 then ArithmeticTemplates254.rho3 a b c + 1
    else if k = 6 then ArithmeticTemplates254.rho4 a b c + 1
    else if k = 7 then ArithmeticTemplates254.rho5 a b c + 1
    else if k = 8 then ArithmeticTemplates254.rho6 a t + 1
    else if k = 9 then ArithmeticTemplates254.rho7 a b c + 1
    else if k = 10 then ArithmeticTemplates254.rho8 a b (first c) (second c) + 1
    else if k = 11 then
      (if c ≠ a ∧ c ≠ b then ArithmeticTemplates254.bundle a b c + 1 else 0)
    else 0

def rowDef : 𝚺₀.Semisentence 5 := .mkSigma
  “r k p u v. ∃ a <⁺ p, ∃ t <⁺ p, !ArithmeticCantor.pairDef p a t ∧
    ∃ b <⁺ p, ∃ c <⁺ p, !ArithmeticCantor.pairDef t b c ∧
    ((k = 0 ∧ ((p = 0 ∧ r = 1) ∨ (p ≠ 0 ∧ r = 0))) ∨
     (k = 1 ∧ !mpDef r a u v) ∨
     (k = 2 ∧ !genDef r a u) ∨
     (k = 3 ∧ ∃ f <⁺ r, !ArithmeticCode254.rho1Def f a t ∧ r = f + 1) ∨
     (k = 4 ∧ ∃ f <⁺ r, !ArithmeticTemplates254.rho2Def f a b c ∧ r = f + 1) ∨
     (k = 5 ∧ ∃ f <⁺ r, !ArithmeticTemplates254.rho3Def f a b c ∧ r = f + 1) ∨
     (k = 6 ∧ ∃ f <⁺ r, !ArithmeticTemplates254.rho4Def f a b c ∧ r = f + 1) ∨
     (k = 7 ∧ ∃ f <⁺ r, !ArithmeticTemplates254.rho5Def f a b c ∧ r = f + 1) ∨
     (k = 8 ∧ ∃ f <⁺ r, !ArithmeticTemplates254.rho6Def f a t ∧ r = f + 1) ∨
     (k = 9 ∧ ∃ f <⁺ r, !ArithmeticTemplates254.rho7Def f a b c ∧ r = f + 1) ∨
     (k = 10 ∧ ∃ d <⁺ p, ∃ e <⁺ p, !ArithmeticCantor.pairDef c d e ∧
       ∃ f <⁺ r, !ArithmeticTemplates254.rho8Def f a b d e ∧ r = f + 1) ∨
     (k = 11 ∧ (((c ≠ a ∧ c ≠ b) ∧ ∃ f <⁺ r,
       !ArithmeticTemplates254.bundleDef f a b c ∧ r = f + 1) ∨
       ((c = a ∨ c = b) ∧ r = 0))) ∨
     ((k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 3 ∧ k ≠ 4 ∧ k ≠ 5 ∧
       k ≠ 6 ∧ k ≠ 7 ∧ k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10 ∧ k ≠ 11) ∧ r = 0))”

lemma payload_fields_flat (p : V) (Q : V → V → V → Prop) :
    (∃ a, a ≤ p ∧ ∃ b c, cantor b c ≤ p ∧ p = cantor a (cantor b c) ∧
      b ≤ p ∧ c ≤ p ∧ Q a b c) ↔
    Q (first p) (first (second p)) (second (second p)) := by
  constructor
  · rintro ⟨a, _, b, c, _, hp, _, _, hQ⟩
    subst p
    simpa only [first_cantor, second_cantor] using hQ
  · intro hQ
    have hp := projections_spec p
    have ht := projections_spec (second p)
    exact ⟨first p, hp.1, first (second p), second (second p),
      by simpa only [cantor_projections] using hp.2.1,
      by simp only [cantor_projections], le_trans ht.1 hp.2.1,
      le_trans ht.2.1 hp.2.1, hQ⟩

instance row_defined : 𝚺₀-Function₄[V] rowKernel via rowDef := .mk fun e => by
  classical
  simp [rowDef, numeral_eq_natCast]
  rw [payload_fields_flat]
  simp only [cantor_projections]
  have hc : second (second (e 2)) ≤ e 2 :=
    le_trans (projections_spec (second (e 2))).2.1 (projections_spec (e 2)).2.1
  simp only [pair_fields _ _ hc]
  by_cases h0 : e 1 = 0
  · by_cases hp : e 2 = 0 <;> simp_all [rowKernel]
  by_cases h1 : e 1 = 1
  · simp_all [rowKernel]
  by_cases h2 : e 1 = 2
  · simp_all [rowKernel]
  by_cases h3 : e 1 = 3
  · simp_all [rowKernel]
  by_cases h4 : e 1 = 4
  · simp_all [rowKernel]
  by_cases h5 : e 1 = 5
  · simp_all [rowKernel]
  by_cases h6 : e 1 = 6
  · simp_all [rowKernel]
  by_cases h7 : e 1 = 7
  · simp_all [rowKernel]
  by_cases h8 : e 1 = 8
  · simp_all [rowKernel]
  by_cases h9 : e 1 = 9
  · simp_all [rowKernel]
  by_cases h10 : e 1 = 10
  · simp_all [rowKernel]
  by_cases h11 : e 1 = 11
  · by_cases hca : second (second (e 2)) = first (e 2) <;>
      by_cases hcb : second (second (e 2)) = first (second (e 2)) <;>
      simp_all [rowKernel]
  simp_all [rowKernel]

/-- Exact live-row adapter for arbitrary child-result oracle and ALL tags.
The first child slot is GEN's tail lookup or MP's minor lookup, respectively.
The second slot is MP's major lookup. No lookup graph is asserted here. -/
theorem rowKernel_nat (rec : Nat → Nat) (tag payload : Nat) :
    rowKernel tag payload
      (if tag = 2 then rec (SetTheory.Cantor.ofNat payload).2
       else rec (SetTheory.Cantor.ofNat (SetTheory.Cantor.ofNat payload).2).1)
      (rec (SetTheory.Cantor.ofNat (SetTheory.Cantor.ofNat payload).2).2) =
    Code254History.row rec tag payload := by
  classical
  match tag with
  | 0 => simp [rowKernel, Code254History.row]
  | 1 => simp [rowKernel, Code254History.row]
  | 2 => simp [rowKernel, Code254History.row]
  | 3 => simp [rowKernel, Code254History.row]
  | 4 => simp [rowKernel, Code254History.row]
  | 5 => simp [rowKernel, Code254History.row]
  | 6 => simp [rowKernel, Code254History.row]
  | 7 => simp [rowKernel, Code254History.row]
  | 8 => simp [rowKernel, Code254History.row]
  | 9 => simp [rowKernel, Code254History.row]
  | 10 => simp [rowKernel, Code254History.row]
  | 11 => simp [rowKernel, Code254History.row]
  | n + 12 =>
      have h1 : n + 12 ≠ 1 := by omega
      simp [rowKernel, Code254History.row, h1]

/-- Explicitly supply the two actual history-query values; this does not
represent the query operation or an oracle as a first-order function. -/
def rowEnv (rec : Nat → Nat) (tag payload output : Nat) : Fin 5 → Nat :=
  ![output, tag, payload,
    if tag = 2 then rec (SetTheory.Cantor.ofNat payload).2
      else rec (SetTheory.Cantor.ofNat (SetTheory.Cantor.ofNat payload).2).1,
    rec (SetTheory.Cantor.ofNat (SetTheory.Cantor.ofNat payload).2).2]

/-- The fixed graph agrees with the actual twelve-case numeric row for every
Nat input and every supplied child-result function, including invalid tags. -/
theorem rowGraph_nat (rec : Nat → Nat) (tag payload output : Nat) :
    rowDef.val.Evalb (rowEnv rec tag payload output) ↔
      output = Code254History.row rec tag payload := by
  have h := (row_defined (V := Nat)).df (rowEnv rec tag payload output)
  change rowDef.val.Evalb (rowEnv rec tag payload output) ↔
    output = rowKernel tag payload
      (if tag = 2 then rec (SetTheory.Cantor.ofNat payload).2
        else rec (SetTheory.Cantor.ofNat (SetTheory.Cantor.ofNat payload).2).1)
      (rec (SetTheory.Cantor.ofNat (SetTheory.Cantor.ofNat payload).2).2) at h
  exact h.trans (Iff.of_eq (congrArg (fun z => output = z) (rowKernel_nat rec tag payload)))

end SetTheory.BusyBeaver.ZFC.ArithmeticRow254
