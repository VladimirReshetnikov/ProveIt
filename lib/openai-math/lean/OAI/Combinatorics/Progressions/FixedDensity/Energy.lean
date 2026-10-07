-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def mean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  𝔼 x, f x

def finsetIndicator {α : Type*} [DecidableEq α]
    (A : Finset α) (x : α) : ℝ :=
  if x ∈ A then 1 else 0

@[simp]
theorem finsetIndicator_of_mem {α : Type*} [DecidableEq α]
    {A : Finset α} {x : α} (hx : x ∈ A) :
    finsetIndicator A x = 1 := by
  simp [finsetIndicator, hx]

@[simp]
theorem finsetIndicator_of_not_mem {α : Type*} [DecidableEq α]
    {A : Finset α} {x : α} (hx : x ∉ A) :
    finsetIndicator A x = 0 := by
  simp [finsetIndicator, hx]

theorem mean_finsetIndicator {α : Type*}
    [Fintype α] [DecidableEq α] (A : Finset α) :
    mean (finsetIndicator A) =
      (A.card : ℝ) / Fintype.card α := by
  rw [mean, Fintype.expect_eq_sum_div_card]
  simp [finsetIndicator]

@[simp]
theorem mean_empty {α : Type*} [Fintype α] [IsEmpty α] (f : α → ℝ) :
    mean f = 0 := by
  simp [mean]

@[simp]
theorem mean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    mean (fun _ : α => c) = c := by
  exact Fintype.expect_const c

@[simp]
theorem mean_zero {α : Type*} [Fintype α] :
    mean (fun _ : α => (0 : ℝ)) = 0 := by
  simp [mean]

theorem mean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g := by
  exact Finset.expect_add_distrib Finset.univ f g

theorem mean_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g := by
  exact Finset.expect_sub_distrib Finset.univ f g

theorem mean_smul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    mean (fun x => c * f x) = c * mean f := by
  exact (Finset.mul_expect Finset.univ f c).symm

theorem mean_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f := by
  rw [mean, Fintype.expect_eq_sum_div_card]
  exact div_nonneg (Finset.sum_nonneg fun x _ => hf x) (Nat.cast_nonneg _)

theorem mean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (hfg : ∀ x, f x ≤ g x) : mean f ≤ mean g := by
  rw [mean, mean, Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun x _ => hfg x) (Nat.cast_nonneg _)

theorem mean_le_of_le_const {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℝ} {c : ℝ} (hf : ∀ x, f x ≤ c) :
    mean f ≤ c := by
  simpa using mean_mono (f := f) (g := fun _ => c) hf

theorem const_le_mean {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℝ} {c : ℝ} (hf : ∀ x, c ≤ f x) :
    c ≤ mean f := by
  simpa using mean_mono (f := fun _ => c) (g := f) hf

noncomputable def mean₂ {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) : ℝ :=
  mean (fun x => mean (f x))

theorem mean₂_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    mean₂ f = mean₂ (fun y x => f x y) := by
  exact Finset.expect_comm Finset.univ Finset.univ f

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def cyclicAPTerm {k N : ℕ} (a d : ZMod N) (j : Fin k) : ZMod N :=
  a + (j : ZMod N) * d

def cyclicAPProduct (k N : ℕ) (f : ZMod N → ℝ)
    (a d : ZMod N) : ℝ :=
  ∏ j : Fin k, f (cyclicAPTerm a d j)

noncomputable def cyclicAPCount (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  mean₂ (fun a d => cyclicAPProduct k N f a d)

theorem cyclicAPProduct_nonneg {k N : ℕ} {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (a d : ZMod N) :
    0 ≤ cyclicAPProduct k N f a d := by
  exact Finset.prod_nonneg fun j _ => hf (cyclicAPTerm a d j)

theorem cyclicAPCount_nonneg {k N : ℕ} [NeZero N]
    {f : ZMod N → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ cyclicAPCount k N f := by
  apply mean_nonneg
  intro a
  apply mean_nonneg
  intro d
  exact cyclicAPProduct_nonneg hf a d

@[simp]
theorem cyclicAPProduct_const (k N : ℕ) (c : ℝ) (a d : ZMod N) :
    cyclicAPProduct k N (fun _ => c) a d = c ^ k := by
  simp [cyclicAPProduct]

theorem cyclicAPProduct_smul
    (k N : ℕ) (c : ℝ) (f : ZMod N → ℝ)
    (a d : ZMod N) :
    cyclicAPProduct k N (fun x => c * f x) a d =
      c ^ k * cyclicAPProduct k N f a d := by
  simp [cyclicAPProduct, Finset.prod_mul_distrib]

@[simp]
theorem cyclicAPCount_const (k N : ℕ) [NeZero N] (c : ℝ) :
    cyclicAPCount k N (fun _ => c) = c ^ k := by
  simp [cyclicAPCount, mean₂]

theorem cyclicAPCount_smul
    (k N : ℕ) [NeZero N] (c : ℝ) (f : ZMod N → ℝ) :
    cyclicAPCount k N (fun x => c * f x) =
      c ^ k * cyclicAPCount k N f := by
  simp_rw [cyclicAPCount, mean₂, cyclicAPProduct_smul, mean_smul]

theorem cyclicAPProduct_mono {k N : ℕ} {f g : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x)
    (a d : ZMod N) :
    cyclicAPProduct k N f a d ≤ cyclicAPProduct k N g a d := by
  exact Finset.prod_le_prod₀
    (fun j _ => hf (cyclicAPTerm a d j))
    (fun j _ => hfg (cyclicAPTerm a d j))

theorem cyclicAPCount_mono {k N : ℕ} [NeZero N]
    {f g : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x) :
    cyclicAPCount k N f ≤ cyclicAPCount k N g := by
  apply mean_mono
  intro a
  apply mean_mono
  intro d
  exact cyclicAPProduct_mono hf hfg a d

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem mean_finset_sum {α κ : Type*}
    [Fintype α]
    (s : Finset κ) (f : κ → α → ℝ) :
    mean (fun x => ∑ q ∈ s, f q x) =
      ∑ q ∈ s, mean (f q) := by
  simpa [mean] using
    (Finset.expect_sum_comm
      (s := (Finset.univ : Finset α)) s
      (fun x q => f q x))

theorem one_sub_sum_le_prod_one_sub
    {κ : Type*} [Fintype κ]
    (I : κ → ℝ)
    (hI0 : ∀ q, 0 ≤ I q)
    (hI01 : ∀ q, I q = 0 ∨ I q = 1) :
    1 - ∑ q, I q ≤ ∏ q, (1 - I q) := by
  by_cases hone : ∃ q, I q = 1
  · obtain ⟨q, hq⟩ := hone
    have hsum : 1 ≤ ∑ r, I r := by
      simpa [hq] using
        (Finset.single_le_sum
          (s := (Finset.univ : Finset κ))
          (f := I) (fun r _ => hI0 r)
          (Finset.mem_univ q))
    have hprod : (∏ r, (1 - I r)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ q)
      rw [hq]
      norm_num
    rw [hprod]
    linarith
  · have hzero : ∀ q, I q = 0 := by
      intro q
      exact (hI01 q).resolve_right fun hq =>
        hone ⟨q, hq⟩
    simp [hzero]

theorem prod_one_sub_le_orderedPair_bonferroni
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (I : κ → ℝ)
    (hI0 : ∀ q, 0 ≤ I q)
    (hI01 : ∀ q, I q = 0 ∨ I q = 1) :
    (∏ q, (1 - I q)) ≤
      1 - ∑ q, I q +
        ∑ q, ∑ r ∈ (Finset.univ : Finset κ).erase q,
          I q * I r := by
  by_cases hone : ∃ q, I q = 1
  · obtain ⟨q, hq⟩ := hone
    have hprod : (∏ r, (1 - I r)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ q)
      rw [hq]
      norm_num
    have hsum :
        (∑ r, I r) =
          1 + ∑ r ∈ (Finset.univ : Finset κ).erase q, I r := by
      rw [← Finset.add_sum_erase
        (Finset.univ : Finset κ) I (Finset.mem_univ q), hq]
    have hrow :
        (∑ r ∈ (Finset.univ : Finset κ).erase q, I r) ≤
          ∑ a, ∑ r ∈ (Finset.univ : Finset κ).erase a,
            I a * I r := by
      calc
        (∑ r ∈ (Finset.univ : Finset κ).erase q, I r) =
            ∑ r ∈ (Finset.univ : Finset κ).erase q,
              I q * I r := by simp [hq]
        _ ≤ ∑ a, ∑ r ∈ (Finset.univ : Finset κ).erase a,
              I a * I r := by
          apply Finset.single_le_sum
            (s := (Finset.univ : Finset κ))
            (f := fun a =>
              ∑ r ∈ (Finset.univ : Finset κ).erase a,
                I a * I r)
          · intro a _
            exact Finset.sum_nonneg fun r _ =>
              mul_nonneg (hI0 a) (hI0 r)
          · exact Finset.mem_univ q
    rw [hprod, hsum]
    linarith
  · have hzero : ∀ q, I q = 0 := by
      intro q
      exact (hI01 q).resolve_right fun hq =>
        hone ⟨q, hq⟩
    simp [hzero]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem mean_prod_type
    {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → ℝ) :
    mean (fun p : α × β => F p.1 p.2) = mean₂ F := by
  simpa [mean, mean₂] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) F)

theorem mean_fin_cons
    {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ) :
    mean F =
      mean₂ (fun a : G => fun y : Fin n → G => F (Fin.cons a y)) := by
  calc
    mean F =
        mean (fun p : G × (Fin n → G) =>
          F (Fin.cons p.1 p.2)) := by
      unfold mean
      apply Fintype.expect_equiv
        (Fin.consEquiv (fun _ : Fin (n + 1) => G)).symm
      intro x
      congr 1
      simp
    _ = mean₂ (fun a : G => fun y : Fin n → G =>
          F (Fin.cons a y)) :=
      mean_prod_type
        (fun a : G => fun y : Fin n → G => F (Fin.cons a y))

theorem prod_mean
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [Nonempty β]
    (F : ι → β → ℝ) :
    (∏ i, mean (F i)) =
      mean (fun y : ι → β => ∏ i, F i (y i)) := by
  classical
  simp_rw [mean, Fintype.expect_eq_sum_div_card]
  rw [Finset.prod_div_distrib, Fintype.prod_sum]
  simp

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def conditionalMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) : ℝ :=
  Finset.expect (P.part x) f

theorem conditionalMean_eq_of_part_eq {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {x y : Ω}
    (hxy : P.part x = P.part y) :
    conditionalMean P f x = conditionalMean P f y := by
  rw [conditionalMean, conditionalMean, hxy]

theorem conditionalMean_eq_of_mem_part {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {x y : Ω}
    (hy : y ∈ P.part x) :
    conditionalMean P f y = conditionalMean P f x := by
  apply conditionalMean_eq_of_part_eq
  apply P.part_eq_of_mem
  · simp
  · exact hy

theorem conditionalMean_nonneg {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Ω) :
    0 ≤ conditionalMean P f x := by
  exact Finset.expect_nonneg fun y _ => hf y

theorem conditionalMean_add {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f g : Ω → ℝ) (x : Ω) :
    conditionalMean P (fun y => f y + g y) x =
      conditionalMean P f x + conditionalMean P g x := by
  exact Finset.expect_add_distrib (P.part x) f g

theorem conditionalMean_sub {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f g : Ω → ℝ) (x : Ω) :
    conditionalMean P (fun y => f y - g y) x =
      conditionalMean P f x - conditionalMean P g x := by
  exact Finset.expect_sub_distrib (P.part x) f g

theorem conditionalMean_smul {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (c : ℝ) (f : Ω → ℝ) (x : Ω) :
    conditionalMean P (fun y => c * f y) x =
      c * conditionalMean P f x := by
  exact (Finset.mul_expect (P.part x) f c).symm

theorem conditionalMean_le_one {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    {f : Ω → ℝ} (hf : ∀ x, f x ≤ 1) (x : Ω) :
    conditionalMean P f x ≤ 1 := by
  apply Finset.expect_le
  · simp
  · exact fun y _ => hf y

@[simp]
theorem conditionalMean_const {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (c : ℝ) (x : Ω) :
    conditionalMean P (fun _ => c) x = c := by
  rw [conditionalMean]
  exact Finset.expect_const (by simp) c

@[simp]
theorem conditionalMean_idem {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean P (conditionalMean P f) x =
      conditionalMean P f x := by
  rw [conditionalMean]
  calc
    Finset.expect (P.part x) (conditionalMean P f) =
        Finset.expect (P.part x)
          (fun _ => conditionalMean P f x) := by
      apply Finset.expect_congr rfl
      intro y hy
      exact conditionalMean_eq_of_mem_part P f hy
    _ = conditionalMean P f x :=
      Finset.expect_const (by simp) _

theorem sum_conditionalMean_on_part {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {s : Finset Ω} (hs : s ∈ P.parts) :
    ∑ x ∈ s, conditionalMean P f x = ∑ x ∈ s, f x := by
  calc
    ∑ x ∈ s, conditionalMean P f x =
        ∑ x ∈ s, Finset.expect s f := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [conditionalMean, P.part_eq_of_mem hs hx]
    _ = (s.card : ℝ) * Finset.expect s f := by
      simp
    _ = ∑ x ∈ s, f x := Finset.card_mul_expect s f

theorem sum_conditionalMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    ∑ x, conditionalMean P f x = ∑ x, f x := by
  classical
  have hparts :
      P.parts.biUnion id = (Finset.univ : Finset Ω) :=
    P.biUnion_parts
  calc
    ∑ x, conditionalMean P f x =
        ∑ x ∈ P.parts.biUnion id, conditionalMean P f x := by
      exact Finset.sum_congr hparts.symm fun _ _ => rfl
    _ =
        ∑ s ∈ P.parts, ∑ x ∈ s, conditionalMean P f x := by
      exact Finset.sum_biUnion P.disjoint
    _ = ∑ s ∈ P.parts, ∑ x ∈ s, f x := by
      apply Finset.sum_congr rfl
      intro s hs
      exact sum_conditionalMean_on_part P f hs
    _ = ∑ x ∈ P.parts.biUnion id, f x :=
      (Finset.sum_biUnion P.disjoint).symm
    _ = ∑ x, f x := by
      exact Finset.sum_congr hparts fun _ _ => rfl

theorem mean_conditionalMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    mean (conditionalMean P f) = mean f := by
  change (𝔼 x, conditionalMean P f x) = 𝔼 x, f x
  rw [Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card, sum_conditionalMean P f]

theorem conditionalMean_sq_le {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean P f x ^ 2 ≤
      conditionalMean P (fun y => f y ^ 2) x := by
  have h :=
    Finset.expect_mul_sq_le_sq_mul_sq
      (P.part x) f (fun _ : Ω => (1 : ℝ))
  simpa [conditionalMean,
    Finset.expect_const (s := P.part x) (by simp) (1 : ℝ)] using h

noncomputable def partitionEnergy {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) : ℝ :=
  mean fun x => conditionalMean P f x ^ 2

theorem partitionEnergy_nonneg {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    0 ≤ partitionEnergy P f := by
  exact mean_nonneg fun x => sq_nonneg _

theorem partitionEnergy_le_mean_sq {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    partitionEnergy P f ≤ mean fun x => f x ^ 2 := by
  calc
    partitionEnergy P f ≤
        mean (conditionalMean P fun x => f x ^ 2) :=
      mean_mono fun x => conditionalMean_sq_le P f x
    _ = mean (fun x => f x ^ 2) :=
      mean_conditionalMean P fun x => f x ^ 2

theorem partitionEnergy_le_one {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    {f : Ω → ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) :
    partitionEnergy P f ≤ 1 := by
  apply mean_le_of_le_const
  intro x
  have h0 := conditionalMean_nonneg P hf0 x
  have h1 := conditionalMean_le_one P hf1 x
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

abbrev FacePartition (Ω : Type*) [Fintype Ω] [DecidableEq Ω] :=
  Finpartition (Finset.univ : Finset Ω)

namespace FacePartition

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem ext_of_part_eq {P Q : FacePartition Ω}
    (h : ∀ x, P.part x = Q.part x) : P = Q := by
  apply Finpartition.ext
  ext s
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hs
    have hxs : Q.part x = s :=
      (h x).symm.trans (P.part_eq_of_mem hs hx)
    rw [← hxs]
    exact Q.part_mem.2 (Finset.mem_univ x)
  · intro hs
    obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hs
    have hxs : P.part x = s :=
      (h x).trans (Q.part_eq_of_mem hs hx)
    rw [← hxs]
    exact P.part_mem.2 (Finset.mem_univ x)

theorem part_subset_of_le {P Q : FacePartition Ω}
    (h : P ≤ Q) (x : Ω) :
    P.part x ⊆ Q.part x := by
  obtain ⟨s, hs, hsub⟩ :=
    h (P.part_mem.2 (Finset.mem_univ x))
  have hxs : x ∈ s :=
    hsub (P.mem_part (Finset.mem_univ x))
  rw [Q.part_eq_of_mem hs hxs]
  exact hsub

theorem le_iff_part_subset {P Q : FacePartition Ω} :
    P ≤ Q ↔ ∀ x, P.part x ⊆ Q.part x := by
  constructor
  · exact fun h x => part_subset_of_le h x
  · intro h s hs
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hs
    refine ⟨Q.part x, Q.part_mem.2 (Finset.mem_univ x), ?_⟩
    rw [← P.part_eq_of_mem hs hx]
    exact h x

def indiscrete : FacePartition Ω :=
  ⊤

def discrete : FacePartition Ω :=
  ⊥

@[simp]
theorem part_indiscrete (x : Ω) :
    (indiscrete : FacePartition Ω).part x = Finset.univ := by
  change (⊤ : FacePartition Ω).part x = Finset.univ
  have hmem :
      (⊤ : FacePartition Ω).part x ∈
        (⊤ : FacePartition Ω).parts :=
    (⊤ : FacePartition Ω).part_mem.2 (Finset.mem_univ x)
  exact Finset.mem_singleton.mp
    (Finpartition.parts_top_subset
      (Finset.univ : Finset Ω) hmem)

@[simp]
theorem part_discrete (x : Ω) :
    (discrete : FacePartition Ω).part x = {x} := by
  apply Finpartition.part_eq_of_mem
  · rw [discrete, Finpartition.mem_bot_iff]
    exact ⟨x, Finset.mem_univ x, rfl⟩
  · exact Finset.mem_singleton_self x

def complexity (P : FacePartition Ω) : ℕ :=
  P.parts.card

noncomputable def representative
    (P : FacePartition Ω) (a : P.parts) : Ω :=
  Classical.choose (P.nonempty_of_mem_parts a.2)

theorem representative_mem
    (P : FacePartition Ω) (a : P.parts) :
    P.representative a ∈ a.1 :=
  Classical.choose_spec (P.nonempty_of_mem_parts a.2)

theorem part_representative
    (P : FacePartition Ω) (a : P.parts) :
    P.part (P.representative a) = a.1 :=
  P.part_eq_of_mem a.2 (P.representative_mem a)

theorem complexity_antitone {P Q : FacePartition Ω}
    (h : P ≤ Q) :
    complexity Q ≤ complexity P :=
  Finpartition.card_mono h

theorem complexity_le_card (P : FacePartition Ω) :
    complexity P ≤ Fintype.card Ω := by
  simpa [complexity] using P.card_parts_le_card

@[simp]
theorem complexity_discrete :
    complexity (discrete : FacePartition Ω) = Fintype.card Ω := by
  simp [complexity, discrete]

@[simp]
theorem complexity_indiscrete [Nonempty Ω] :
    complexity (indiscrete : FacePartition Ω) = 1 := by
  let x : Ω := Classical.choice inferInstance
  have huniv :
      (Finset.univ : Finset Ω) ∈
        (⊤ : FacePartition Ω).parts := by
    have hx :=
      (⊤ : FacePartition Ω).part_mem.2
        (Finset.mem_univ x)
    change
      (indiscrete : FacePartition Ω).part x ∈
        (indiscrete : FacePartition Ω).parts at hx
    rw [part_indiscrete] at hx
    exact hx
  have hparts :
      (⊤ : FacePartition Ω).parts =
        {(Finset.univ : Finset Ω)} := by
    apply Finset.Subset.antisymm
    · exact Finpartition.parts_top_subset _
    · intro s hs
      rw [Finset.mem_singleton] at hs
      simpa [hs] using huniv
  simp [complexity, indiscrete, hparts]

def join (P Q : FacePartition Ω) : FacePartition Ω :=
  P ⊓ Q

theorem join_le_left (P Q : FacePartition Ω) :
    join P Q ≤ P :=
  inf_le_left

theorem join_le_right (P Q : FacePartition Ω) :
    join P Q ≤ Q :=
  inf_le_right

theorem le_join_iff {P Q R : FacePartition Ω} :
    R ≤ join P Q ↔ R ≤ P ∧ R ≤ Q :=
  le_inf_iff

@[simp]
theorem part_join (P Q : FacePartition Ω) (x : Ω) :
    (join P Q).part x = P.part x ∩ Q.part x := by
  apply Finpartition.part_eq_of_mem
  · rw [join, Finpartition.parts_inf]
    apply Finset.mem_erase.mpr
    constructor
    · exact Finset.nonempty_iff_ne_empty.mp ⟨x, by simp⟩
    · apply Finset.mem_image.mpr
      refine ⟨(P.part x, Q.part x), ?_, rfl⟩
      simp
  · simp

theorem complexity_join_le (P Q : FacePartition Ω) :
    complexity (join P Q) ≤ complexity P * complexity Q := by
  change (P ⊓ Q).parts.card ≤ P.parts.card * Q.parts.card
  calc
    (P ⊓ Q).parts.card =
        (((P.parts ×ˢ Q.parts).image
          (fun st => st.1 ⊓ st.2)).erase ⊥).card :=
      congrArg Finset.card (Finpartition.parts_inf P Q)
    _ ≤
        ((P.parts ×ˢ Q.parts).image
          (fun st => st.1 ⊓ st.2)).card :=
      Finset.card_le_card (Finset.erase_subset _ _)
    _ ≤ (P.parts ×ˢ Q.parts).card :=
      Finset.card_image_le
    _ = P.parts.card * Q.parts.card :=
      Finset.card_product P.parts Q.parts

def joinFinset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → FacePartition Ω) :
    FacePartition Ω :=
  s.inf P

@[simp]
theorem joinFinset_empty {ι : Type*} [DecidableEq ι]
    (P : ι → FacePartition Ω) :
    joinFinset ∅ P = indiscrete :=
  rfl

@[simp]
theorem joinFinset_insert {ι : Type*} [DecidableEq ι]
    (a : ι) (s : Finset ι) (P : ι → FacePartition Ω) :
    joinFinset (insert a s) P =
      join (P a) (joinFinset s P) := by
  simp [joinFinset, join]

theorem joinFinset_le_of_mem {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (P : ι → FacePartition Ω)
    {i : ι} (hi : i ∈ s) :
    joinFinset s P ≤ P i :=
  Finset.inf_le hi

theorem le_joinFinset_iff {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {P : ι → FacePartition Ω}
    {Q : FacePartition Ω} :
    Q ≤ joinFinset s P ↔ ∀ i ∈ s, Q ≤ P i :=
  Finset.le_inf_iff

theorem mem_part_joinFinset_iff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → FacePartition Ω)
    (x y : Ω) :
    y ∈ (joinFinset s P).part x ↔
      ∀ i ∈ s, y ∈ (P i).part x := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [joinFinset_empty]
      simp
  | @insert a s ha ih =>
      simp only [joinFinset_insert, part_join,
        Finset.mem_inter, Finset.mem_insert, forall_eq_or_imp,
        ih]

theorem complexity_joinFinset_le [Nonempty Ω]
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → FacePartition Ω) :
    complexity (joinFinset s P) ≤
      ∏ i ∈ s, complexity (P i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      change complexity (indiscrete : FacePartition Ω) ≤ 1
      simp
  | @insert a s ha ih =>
      calc
        complexity (joinFinset (insert a s) P) ≤
            complexity (P a) *
              complexity (joinFinset s P) := by
          rw [joinFinset_insert]
          exact complexity_join_le _ _
        _ ≤
            complexity (P a) *
              (∏ i ∈ s, complexity (P i)) :=
          Nat.mul_le_mul_left _ ih
        _ = ∏ i ∈ insert a s, complexity (P i) := by
          simp [ha]

def generatedBy (F : Finset (Finset Ω)) : FacePartition Ω :=
  Finpartition.atomise Finset.univ F

@[simp]
theorem mem_part_generatedBy_iff (F : Finset (Finset Ω))
    (x y : Ω) :
    y ∈ (generatedBy F).part x ↔
      ∀ s ∈ F, (x ∈ s ↔ y ∈ s) := by
  classical
  let P : FacePartition Ω := generatedBy F
  have hp : P.part x ∈ P.parts :=
    P.part_mem.2 (Finset.mem_univ x)
  have hpAtom :
      P.part x ∈
        (Finpartition.atomise
          (Finset.univ : Finset Ω) F).parts := by
    change
      (Finpartition.atomise
        (Finset.univ : Finset Ω) F).part x ∈
        (Finpartition.atomise
          (Finset.univ : Finset Ω) F).parts at hp
    exact hp
  obtain ⟨_, Q, hQ, hpart⟩ :=
    Finpartition.mem_atomise.mp hpAtom
  have hmem := Finset.ext_iff.mp hpart
  have hx : x ∈ P.part x :=
    P.mem_part (Finset.mem_univ x)
  have hxAtom := (hmem x).2 hx
  simp only [Finset.mem_filter] at hxAtom
  constructor
  · intro hy s hs
    have hyAtom := (hmem y).2 hy
    simp only [Finset.mem_filter] at hyAtom
    exact (hxAtom.2 s hs).symm.trans (hyAtom.2 s hs)
  · intro hsignature
    apply (hmem y).1
    simp only [Finset.mem_filter]
    refine ⟨Finset.mem_univ y, ?_⟩
    intro s hs
    exact (hxAtom.2 s hs).trans (hsignature s hs)

theorem generatedBy_antitone {F G : Finset (Finset Ω)}
    (hFG : F ⊆ G) :
    generatedBy G ≤ generatedBy F := by
  rw [le_iff_part_subset]
  intro x y hy
  rw [mem_part_generatedBy_iff] at hy ⊢
  intro s hs
  exact hy s (hFG hs)

theorem complexity_generatedBy_le (F : Finset (Finset Ω)) :
    complexity (generatedBy F) ≤ 2 ^ F.card := by
  exact Finpartition.card_atomise_le

@[simp]
theorem generatedBy_empty :
    generatedBy (∅ : Finset (Finset Ω)) =
      indiscrete := by
  apply ext_of_part_eq
  intro x
  ext y
  simp [mem_part_generatedBy_iff, part_indiscrete]

theorem generatedBy_union
    (F G : Finset (Finset Ω)) :
    generatedBy (F ∪ G) =
      join (generatedBy F) (generatedBy G) := by
  apply ext_of_part_eq
  intro x
  ext y
  simp only [part_join, Finset.mem_inter,
    mem_part_generatedBy_iff]
  simp only [Finset.mem_union]
  constructor
  · intro h
    constructor
    · intro s hs
      exact h s (Or.inl hs)
    · intro s hs
      exact h s (Or.inr hs)
  · rintro ⟨hF, hG⟩ s (hs | hs)
    · exact hF s hs
    · exact hG s hs

theorem generatedBy_insert
    (A : Finset Ω) (F : Finset (Finset Ω)) :
    generatedBy (insert A F) =
      join (generatedBy F)
        (generatedBy ({A} : Finset (Finset Ω))) := by
  rw [show insert A F = F ∪ {A} by
    ext s
    simp]
  exact generatedBy_union F {A}

abbrev atomSetoid (P : FacePartition Ω) : Setoid Ω :=
  Setoid.ker P.part

@[simp]
theorem atomSetoid_rel (P : FacePartition Ω) (x y : Ω) :
    atomSetoid P x y ↔ P.part x = P.part y :=
  Iff.rfl

def pullbackSetoid {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) : Setoid Ω where
  r x y := Q.part (f x) = Q.part (f y)
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂ }

instance instDecidableRelPullbackSetoid {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) :
    DecidableRel (pullbackSetoid f Q) := by
  intro x y
  change Decidable (Q.part (f x) = Q.part (f y))
  infer_instance

def pullback {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) : FacePartition Ω :=
  Finpartition.ofSetoid (pullbackSetoid f Q)

@[simp]
theorem mem_part_pullback_iff {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) (x y : Ω) :
    y ∈ (pullback f Q).part x ↔
      Q.part (f x) = Q.part (f y) := by
  change
    y ∈
        (Finpartition.ofSetoid
          (pullbackSetoid f Q)).part x ↔
      Q.part (f x) = Q.part (f y)
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

theorem mem_part_pullback_iff_image_mem {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) (x y : Ω) :
    y ∈ (pullback f Q).part x ↔
      f y ∈ Q.part (f x) := by
  rw [mem_part_pullback_iff]
  constructor
  · intro h
    exact
      (Q.mem_part_iff_part_eq_part
        (Finset.mem_univ (f y))
        (Finset.mem_univ (f x))).2 h.symm
  · intro h
    exact
      ((Q.mem_part_iff_part_eq_part
        (Finset.mem_univ (f y))
        (Finset.mem_univ (f x))).1 h).symm

theorem part_pullback_eq_filter {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) (x : Ω) :
    (pullback f Q).part x =
      Finset.univ.filter (fun y => f y ∈ Q.part (f x)) := by
  ext y
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact mem_part_pullback_iff_image_mem f Q x y

theorem pullback_mono {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) {P Q : FacePartition Λ}
    (h : P ≤ Q) :
    pullback f P ≤ pullback f Q := by
  rw [le_iff_part_subset]
  intro x y hy
  rw [mem_part_pullback_iff_image_mem] at hy ⊢
  exact part_subset_of_le h (f x) hy

@[simp]
theorem pullback_id (P : FacePartition Ω) :
    pullback id P = P := by
  apply ext_of_part_eq
  intro x
  ext y
  simp only [mem_part_pullback_iff_image_mem, id_eq]

theorem pullback_comp {Λ Γ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    [Fintype Γ] [DecidableEq Γ]
    (f : Ω → Λ) (g : Γ → Ω) (Q : FacePartition Λ) :
    pullback g (pullback f Q) =
      pullback (f ∘ g) Q := by
  apply ext_of_part_eq
  intro x
  ext y
  simp only [mem_part_pullback_iff_image_mem,
    Function.comp_apply]

theorem complexity_pullback_le {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) :
    complexity (pullback f Q) ≤ complexity Q := by
  classical
  let R : FacePartition Ω := pullback f Q
  let representative : R.parts → Ω := fun s =>
    Classical.choose (R.nonempty_of_mem_parts s.2)
  have representative_mem (s : R.parts) :
      representative s ∈ s.1 :=
    Classical.choose_spec (R.nonempty_of_mem_parts s.2)
  let atomMap : R.parts → Q.parts := fun s =>
    ⟨Q.part (f (representative s)),
      Q.part_mem.2 (Finset.mem_univ _)⟩
  have atomMap_injective : Function.Injective atomMap := by
    intro s t hst
    apply Subtype.ext
    have htarget :=
      congrArg (fun u : Q.parts => u.1) hst
    change
      Q.part (f (representative s)) =
        Q.part (f (representative t)) at htarget
    have htInPart :
        representative t ∈ R.part (representative s) := by
      change
        representative t ∈
          (pullback f Q).part (representative s)
      exact
        (mem_part_pullback_iff f Q
          (representative s) (representative t)).2 htarget
    have htInS : representative t ∈ s.1 := by
      rw [← R.part_eq_of_mem s.2 (representative_mem s)]
      exact htInPart
    exact
      R.eq_of_mem_parts s.2 t.2 htInS
        (representative_mem t)
  have hcard :=
    Fintype.card_le_of_injective atomMap atomMap_injective
  simpa only [complexity, R, Fintype.card_coe] using hcard

end FacePartition

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem sum_conditionalMean_on_coarser_part
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) {s : Finset Ω} (hs : s ∈ Q.parts) :
    ∑ x ∈ s, conditionalMean P f x = ∑ x ∈ s, f x := by
  let fineParts : Finset (Finset Ω) :=
    P.parts.filter (fun t => t ⊆ s)
  have hUnion : fineParts.biUnion id = s := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp ht).2 hxt
    · intro hxs
      obtain ⟨t, ht, hxt⟩ :=
        P.exists_mem (Finset.mem_univ x)
      obtain ⟨u, hu, htu⟩ := hPQ ht
      have hus : u = s :=
        Q.eq_of_mem_parts hu hs (htu hxt) hxs
      have hts : t ⊆ s := by
        simpa [hus] using htu
      exact Finset.mem_biUnion.mpr
        ⟨t, Finset.mem_filter.mpr ⟨ht, hts⟩, hxt⟩
  have hdisjoint :
      (↑fineParts : Set (Finset Ω)).PairwiseDisjoint id := by
    apply Set.Pairwise.mono ?_ P.disjoint
    intro t ht
    exact (Finset.mem_filter.mp ht).1
  calc
    ∑ x ∈ s, conditionalMean P f x =
        ∑ x ∈ fineParts.biUnion id,
          conditionalMean P f x := by
      exact Finset.sum_congr hUnion.symm fun _ _ => rfl
    _ =
        ∑ t ∈ fineParts,
          ∑ x ∈ t, conditionalMean P f x :=
      Finset.sum_biUnion hdisjoint
    _ = ∑ t ∈ fineParts, ∑ x ∈ t, f x := by
      apply Finset.sum_congr rfl
      intro t ht
      exact sum_conditionalMean_on_part P f
        (Finset.mem_filter.mp ht).1
    _ = ∑ x ∈ fineParts.biUnion id, f x :=
      (Finset.sum_biUnion hdisjoint).symm
    _ = ∑ x ∈ s, f x := by
      exact Finset.sum_congr hUnion fun _ _ => rfl

@[simp]
theorem conditionalMean_tower_of_le
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean Q (conditionalMean P f) x =
      conditionalMean Q f x := by
  change
    Finset.expect (Q.part x) (conditionalMean P f) =
      Finset.expect (Q.part x) f
  rw [Finset.expect_eq_sum_div_card,
    Finset.expect_eq_sum_div_card,
    sum_conditionalMean_on_coarser_part P Q hPQ f
      (Q.part_mem.2 (Finset.mem_univ x))]

@[simp]
theorem conditionalMean_reverse_tower_of_le
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean P (conditionalMean Q f) x =
      conditionalMean Q f x := by
  rw [conditionalMean]
  calc
    Finset.expect (P.part x) (conditionalMean Q f) =
        Finset.expect (P.part x)
          (fun _ => conditionalMean Q f x) := by
      apply Finset.expect_congr rfl
      intro y hy
      exact conditionalMean_eq_of_mem_part Q f
        (FacePartition.part_subset_of_le hPQ x hy)
    _ = conditionalMean Q f x :=
      Finset.expect_const (by simp) _

theorem conditionalMean_mul_right_of_constant_on_part
    (P : FacePartition Ω) (u v : Ω → ℝ) (x : Ω)
    (hv : ∀ y ∈ P.part x, v y = v x) :
    conditionalMean P (fun y => u y * v y) x =
      conditionalMean P u x * v x := by
  calc
    conditionalMean P (fun y => u y * v y) x =
        conditionalMean P (fun y => v x * u y) x := by
      rw [conditionalMean, conditionalMean]
      apply Finset.expect_congr rfl
      intro y hy
      rw [hv y hy]
      ring
    _ = v x * conditionalMean P u x :=
      conditionalMean_smul P (v x) u x
    _ = conditionalMean P u x * v x := by
      ring

theorem conditionalMean_mul_conditionalMean_right
    (P : FacePartition Ω) (u v : Ω → ℝ) (x : Ω) :
    conditionalMean P
        (fun y => u y * conditionalMean P v y) x =
      conditionalMean P u x * conditionalMean P v x := by
  apply conditionalMean_mul_right_of_constant_on_part
  intro y hy
  exact conditionalMean_eq_of_mem_part P v hy

theorem mean_conditionalMean_mul_eq_sq_of_le
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    mean (fun x =>
      conditionalMean P f x * conditionalMean Q f x) =
      mean (fun x => conditionalMean Q f x ^ 2) := by
  calc
    mean (fun x =>
        conditionalMean P f x * conditionalMean Q f x) =
        mean (conditionalMean Q (fun x =>
          conditionalMean P f x * conditionalMean Q f x)) :=
      (mean_conditionalMean Q _).symm
    _ =
        mean (fun x =>
          conditionalMean Q (conditionalMean P f) x *
            conditionalMean Q f x) := by
      apply congrArg mean
      funext x
      exact conditionalMean_mul_conditionalMean_right
        Q (conditionalMean P f) f x
    _ =
        mean (fun x =>
          conditionalMean Q f x * conditionalMean Q f x) := by
      apply congrArg mean
      funext x
      rw [conditionalMean_tower_of_le P Q hPQ]
    _ = mean (fun x => conditionalMean Q f x ^ 2) := by
      apply congrArg mean
      funext x
      rw [pow_two]

theorem partitionEnergy_pythagorean
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    partitionEnergy P f =
      partitionEnergy Q f +
        mean (fun x =>
          (conditionalMean P f x -
            conditionalMean Q f x) ^ 2) := by
  have hcross :=
    mean_conditionalMean_mul_eq_sq_of_le P Q hPQ f
  have hdiff :
      mean (fun x =>
        (conditionalMean P f x -
          conditionalMean Q f x) ^ 2) =
        mean (fun x => conditionalMean P f x ^ 2) -
          2 * mean (fun x =>
            conditionalMean P f x * conditionalMean Q f x) +
          mean (fun x => conditionalMean Q f x ^ 2) := by
    calc
      mean (fun x =>
          (conditionalMean P f x -
            conditionalMean Q f x) ^ 2) =
          mean (fun x =>
            conditionalMean P f x ^ 2 -
              2 * (conditionalMean P f x *
                conditionalMean Q f x) +
              conditionalMean Q f x ^ 2) := by
        apply congrArg mean
        funext x
        ring
      _ =
          mean (fun x => conditionalMean P f x ^ 2) -
            2 * mean (fun x =>
              conditionalMean P f x * conditionalMean Q f x) +
            mean (fun x => conditionalMean Q f x ^ 2) := by
        rw [mean_add, mean_sub, mean_smul]
  change
    mean (fun x => conditionalMean P f x ^ 2) =
      mean (fun x => conditionalMean Q f x ^ 2) +
        mean (fun x =>
          (conditionalMean P f x -
            conditionalMean Q f x) ^ 2)
  rw [hdiff, hcross]
  ring

theorem partitionEnergy_sub_eq_mean_sq
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    partitionEnergy P f - partitionEnergy Q f =
      mean (fun x =>
        (conditionalMean P f x -
          conditionalMean Q f x) ^ 2) := by
  rw [partitionEnergy_pythagorean P Q hPQ f]
  ring

theorem partitionEnergy_mono
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    partitionEnergy Q f ≤ partitionEnergy P f := by
  rw [partitionEnergy_pythagorean P Q hPQ f]
  exact le_add_of_nonneg_right
    (mean_nonneg fun x => sq_nonneg _)

theorem partitionEnergy_mem_Icc [Nonempty Ω]
    (P : FacePartition Ω) {f : Ω → ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) :
    partitionEnergy P f ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨partitionEnergy_nonneg P f,
    partitionEnergy_le_one P hf0 hf1⟩

theorem partitionEnergy_refinement_bounds [Nonempty Ω]
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    {f : Ω → ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) :
    0 ≤ partitionEnergy Q f ∧
      partitionEnergy Q f ≤ partitionEnergy P f ∧
      partitionEnergy P f ≤ 1 :=
  ⟨partitionEnergy_nonneg Q f,
    partitionEnergy_mono P Q hPQ f,
    partitionEnergy_le_one P hf0 hf1⟩

end Erdos3.FixedDensity

end

end OAI
