import IPRADerivations.Algebra.QuadraticTowerMultiplicationHeight
import IPRADerivations.Foundations.GuardedTotalization

/-!
# Three-call sign recipe and genuine lower operand bounds

For source isoperimetric_ipra equation2.3 the first two lower sign queries
read a and b. The third reads d when sign(a)=0 and otherwise reads the
actual computed norm a*a-d*(b*b). Thus the zero-radicand case uses three
lower sign queries, rather than adding a fourth unconditional query.
All norm arithmetic uses the original checked multiplication table.

Lower sign reads are explicitly totalized modulo3; proved valid lower
tags are unchanged. This module constructs the actual local recipe and
derives its operand height and address bounds from original input heights.
The recursive sign table and ordered-extension correctness are separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerSignRecipe

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open QuadraticTowerCoefficients (width)
open QuadraticTowerArrayCodec (arrayHeight code horizon)
open QuadraticTowerScalarBudget (growth amp)
open QuadraticTowerMultiplicationTable (leftHalf rightHalf budget query)
open QuadraticTowerMultiplicationHeight (radicandsHeight)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open LeanProofs.IPRA.Foundations.BoundedReflection
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero sel_cases)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def read (h B S A : PTm n) : PTm n := rem (entry S (code h A B)) (succ two)
def firstTag (h B D S A : PTm n) : PTm n := read h (budget h B D) S (leftHalf h A)
def secondTag (h B D S A : PTm n) : PTm n := read h (budget h B D) S (rightHalf h A)
def norm (h B D A : PTm n) : PTm n :=
  let K := budget h B D
  let a := leftHalf h A
  let b := rightHalf h A
  let aa := query h K D a a
  let bb := query h K D b b
  let dbb := query h K D (entry D h) bb
  QuadraticTowerCoefficientArithmetic.added h aa (QuadraticTowerCoefficientArithmetic.negated h dbb)
def thirdInput (h B D S A : PTm n) : PTm n :=
  sel (eqb (firstTag h B D S A) zero) (entry D h) (norm h B D A)
def thirdTag (h B D S A : PTm n) : PTm n := read h (budget h B D) S (thirdInput h B D S A)
def tagProduct (s t : PTm n) : PTm n := sel (eqb s zero) zero
  (sel (eqb t zero) zero (sel (eqb s t) one two))
def dispatch (s t u : PTm n) : PTm n := sel (eqb s zero) (tagProduct t u)
  (sel (eqb t zero) s (sel (eqb s t) s (tagProduct s u)))
def recipe (h B D S A : PTm n) : PTm n :=
  dispatch (firstTag h B D S A) (secondTag h B D S A) (thirdTag h B D S A)

@[simp] theorem subst_read {k : ℕ} (σ : Fin n → PTm k) (h B S A : PTm n) :
    Syn.subst σ (read h B S A) = read (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ S) (Syn.subst σ A) := by simp [read]
@[simp] theorem subst_firstTag {k : ℕ} (σ : Fin n → PTm k) (h B D S A : PTm n) :
    Syn.subst σ (firstTag h B D S A) = firstTag (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ S) (Syn.subst σ A) := by simp [firstTag]
@[simp] theorem subst_secondTag {k : ℕ} (σ : Fin n → PTm k) (h B D S A : PTm n) :
    Syn.subst σ (secondTag h B D S A) = secondTag (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ S) (Syn.subst σ A) := by simp [secondTag]
@[simp] theorem subst_norm {k : ℕ} (σ : Fin n → PTm k) (h B D A : PTm n) :
    Syn.subst σ (norm h B D A) = norm (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) := by simp [norm]
@[simp] theorem subst_thirdInput {k : ℕ} (σ : Fin n → PTm k) (h B D S A : PTm n) :
    Syn.subst σ (thirdInput h B D S A) = thirdInput (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ S) (Syn.subst σ A) := by simp [thirdInput,sel]
@[simp] theorem subst_thirdTag {k : ℕ} (σ : Fin n → PTm k) (h B D S A : PTm n) :
    Syn.subst σ (thirdTag h B D S A) = thirdTag (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ S) (Syn.subst σ A) := by simp [thirdTag]
@[simp] theorem subst_tagProduct {k : ℕ} (σ : Fin n → PTm k) (s t : PTm n) :
    Syn.subst σ (tagProduct s t) = tagProduct (Syn.subst σ s) (Syn.subst σ t) := by simp [tagProduct,sel]
@[simp] theorem subst_dispatch {k : ℕ} (σ : Fin n → PTm k) (s t u : PTm n) :
    Syn.subst σ (dispatch s t u) = dispatch (Syn.subst σ s) (Syn.subst σ t) (Syn.subst σ u) := by simp [dispatch,sel]
@[simp] theorem subst_recipe {k : ℕ} (σ : Fin n → PTm k) (h B D S A : PTm n) :
    Syn.subst σ (recipe h B D S A) = recipe (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ S) (Syn.subst σ A) := by simp [recipe]

theorem read_bound (h B S A : PTm n) : Γ ⊢[PRAAx] lt (read h B S A) (succ two) :=
  .andE₂ (Foundations.RuntimeWordAppend.divide_spec _ _ (zero_lt_succ two))

theorem read_exact (h B S A : PTm n)
    (hTag : Γ ⊢[PRAAx] lt (entry S (code h A B)) (succ two)) : Γ ⊢[PRAAx]
    read h B S A ≐ entry S (code h A B) :=
  Foundations.RuntimeWordAppend.remainder_small _ _ (zero_lt_succ two) hTag

theorem negated_height (h A b : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    arrayHeight h (QuadraticTowerCoefficientArithmetic.negated h A) b := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] arrayHeight (Syn.shift h) (Syn.shift A) (Syn.shift b) := by
    simpa only [Fm.shift,QuadraticTowerArrayCodec.subst_arrayHeight,Syn.shift] using ha.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (Syn.shift h)) := Prf.hyp0
  have scalar := QuadraticTowerScalarBudget.negative_height _ _
    (QuadraticTowerArrayCodec.height_at (Syn.shift h) (Syn.shift A) (Syn.shift b) (var 0) hs.wk hi)
  simpa only [Δ,Syn.shift,QuadraticTowerCoefficientArithmetic.subst_negated] using
    QuadraticTowerScalarBudget.height_congr (QuadraticTowerCoefficientArithmetic.negated_lookup _ _ _ hi).eqSymm
      (.eqRefl _) scalar

theorem norm_height (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    arrayHeight h (norm h B D A) (growth (QuadraticTowerGrowth.path (succ h)) b) := by
  let K := budget h B D
  let g := growth (QuadraticTowerGrowth.path h) b
  let g2 := growth (QuadraticTowerGrowth.path h) g
  have bg : Γ ⊢[PRAAx] le b g := QuadraticTowerGrowth.growth_inflation _ _
  have gK : Γ ⊢[PRAAx] le g K := QuadraticTowerGrowth.lower_path_budget h B D b hb
  have bK := le_trans bg gK
  have rh := QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b hD (le_succ_self h)
  have a0 := QuadraticTowerMultiplicationHeight.left_height h A b ha
  have a1 := QuadraticTowerMultiplicationHeight.right_height h A b ha
  have aa : Γ ⊢[PRAAx] arrayHeight h (query h K D (leftHalf h A) (leftHalf h A)) g :=
    QuadraticTowerMultiplicationHeight.query_height h K D _ _ b bK rh a0 a0
  have bb : Γ ⊢[PRAAx] arrayHeight h (query h K D (rightHalf h A) (rightHalf h A)) g :=
    QuadraticTowerMultiplicationHeight.query_height h K D _ _ b bK rh a1 a1
  have dH := QuadraticTowerMultiplicationHeight.array_mono h (entry D h) b g
    (QuadraticTowerMultiplicationHeight.radicand_at D (succ h) b h hD (le_refl _)) bg
  have dbb : Γ ⊢[PRAAx] arrayHeight h (query h K D (entry D h) (query h K D (rightHalf h A) (rightHalf h A))) g2 :=
    QuadraticTowerMultiplicationHeight.query_height h K D _ _ g gK
      (QuadraticTowerMultiplicationHeight.radicands_mono D h b g rh bg) dH bb
  have sum := QuadraticTowerMultiplicationHeight.added_height h _ _ g2
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ aa (QuadraticTowerGrowth.growth_inflation _ _))
      (negated_height _ _ _ dbb)
  exact QuadraticTowerMultiplicationHeight.array_congr (.eqRefl _) (.eqRefl _)
    (QuadraticTowerGrowth.twice_then_add h b) sum

theorem third_input_height (h B D S A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    arrayHeight h (thirdInput h B D S A) (growth (QuadraticTowerGrowth.path (succ h)) b) := by
  have selected : Γ ⊢[PRAAx] thirdInput h B D S A ≐ entry D h ⋎ thirdInput h B D S A ≐ norm h B D A :=
    sel_cases (eqb_cases _ _)
  refine .orE selected ?_ ?_
  · exact QuadraticTowerMultiplicationHeight.array_congr (.eqRefl _) Prf.hyp0.eqSymm (.eqRefl _)
      (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _
        (QuadraticTowerMultiplicationHeight.radicand_at D (succ h) b h hD.wk (le_refl _))
        (QuadraticTowerGrowth.growth_inflation _ _))
  · exact QuadraticTowerMultiplicationHeight.array_congr (.eqRefl _) Prf.hyp0.eqSymm (.eqRefl _)
      (norm_height h B D A b hb.wk hD.wk ha.wk)

theorem third_input_fits (h B D S A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    arrayHeight h (thirdInput h B D S A) (budget h B D) :=
  QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ (third_input_height h B D S A b hb hD ha)
    (QuadraticTowerGrowth.path_growth_budget h B D b hb)

theorem sign_operand_addresses (h B D S A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    lt (code h (leftHalf h A) (budget h B D)) (horizon h (budget h B D)) ⋏
      (lt (code h (rightHalf h A) (budget h B D)) (horizon h (budget h B D)) ⋏
        lt (code h (thirdInput h B D S A) (budget h B D)) (horizon h (budget h B D))) := by
  have bK := le_trans (QuadraticTowerGrowth.growth_inflation (QuadraticTowerGrowth.path h) b)
    (QuadraticTowerGrowth.lower_path_budget h B D b hb)
  exact .andI (QuadraticTowerArrayCodec.code_bound _ _ _
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ (QuadraticTowerMultiplicationHeight.left_height h A b ha) bK))
      (.andI (QuadraticTowerArrayCodec.code_bound _ _ _
        (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ (QuadraticTowerMultiplicationHeight.right_height h A b ha) bK))
        (QuadraticTowerArrayCodec.code_bound _ _ _ (third_input_fits h B D S A b hb hD ha)))

theorem select_bound (g a b N : PTm n) (hg : Γ ⊢[PRAAx] Foundations.BooleanBits.Bit g)
    (ha : Γ ⊢[PRAAx] lt a N) (hb : Γ ⊢[PRAAx] lt b N) : Γ ⊢[PRAAx] lt (sel g a b) N :=
  .orE (sel_cases hg)
    (lt_congr Prf.hyp0.eqSymm (.eqRefl _) ha.wk)
    (lt_congr Prf.hyp0.eqSymm (.eqRefl _) hb.wk)

theorem tag_product_bound (s t : PTm n) : Γ ⊢[PRAAx] lt (tagProduct s t) (succ two) := by
  have h0 : Γ ⊢[PRAAx] lt zero (succ two) := zero_lt_succ two
  have h1 : Γ ⊢[PRAAx] lt one (succ two) := le_succ_self two
  have h2 : Γ ⊢[PRAAx] lt two (succ two) := le_refl _
  have inner : Γ ⊢[PRAAx] lt (sel (eqb s t) one two) (succ two) :=
    select_bound (eqb s t) one two (succ two) (eqb_cases s t) h1 h2
  have middle : Γ ⊢[PRAAx] lt (sel (eqb t zero) zero (sel (eqb s t) one two)) (succ two) :=
    select_bound _ _ _ _ (eqb_cases t zero) h0 inner
  exact select_bound _ _ _ _ (eqb_cases s zero) h0 middle

theorem dispatch_bound (s t u : PTm n) (hs : Γ ⊢[PRAAx] lt s (succ two)) : Γ ⊢[PRAAx]
    lt (dispatch s t u) (succ two) := by
  have inner : Γ ⊢[PRAAx] lt (sel (eqb s t) s (tagProduct s u)) (succ two) :=
    select_bound _ _ _ _ (eqb_cases s t) hs (tag_product_bound s u)
  have middle : Γ ⊢[PRAAx] lt (sel (eqb t zero) s (sel (eqb s t) s (tagProduct s u))) (succ two) :=
    select_bound _ _ _ _ (eqb_cases t zero) hs inner
  exact select_bound _ _ _ _ (eqb_cases s zero) (tag_product_bound t u) middle

theorem recipe_bound (h B D S A : PTm n) : Γ ⊢[PRAAx] lt (recipe h B D S A) (succ two) :=
  dispatch_bound (firstTag h B D S A) (secondTag h B D S A) (thirdTag h B D S A)
    (read_bound h (budget h B D) S (leftHalf h A))

theorem third_when_a_zero (h B D S A : PTm n) (ha : Γ ⊢[PRAAx] firstTag h B D S A ≐ zero) : Γ ⊢[PRAAx]
    thirdInput h B D S A ≐ entry D h := sel_one (eqb_of_eq ha)

theorem third_when_a_nonzero (h B D S A : PTm n) (ha : Γ ⊢[PRAAx] neg (firstTag h B D S A ≐ zero)) : Γ ⊢[PRAAx]
    thirdInput h B D S A ≐ norm h B D A := sel_zero (eqb_of_ne ha)

theorem tag_product_zero_left (s t : PTm n) (hs : Γ ⊢[PRAAx] s ≐ zero) : Γ ⊢[PRAAx]
    tagProduct s t ≐ zero := sel_one (eqb_of_eq hs)

theorem tag_product_zero_right (s t : PTm n) (ht : Γ ⊢[PRAAx] t ≐ zero) : Γ ⊢[PRAAx]
    tagProduct s t ≐ zero := by
  refine .orE (eqb_cases s zero) ?_ ?_
  · exact (sel_zero Prf.hyp0).eqTrans (sel_one (eqb_of_eq ht.wk))
  · exact sel_one Prf.hyp0

theorem dispatch_a_zero (s t u : PTm n) (hs : Γ ⊢[PRAAx] s ≐ zero) : Γ ⊢[PRAAx]
    dispatch s t u ≐ tagProduct t u := sel_one (eqb_of_eq hs)

theorem dispatch_b_zero (s t u : PTm n) (hs : Γ ⊢[PRAAx] neg (s ≐ zero)) (ht : Γ ⊢[PRAAx] t ≐ zero) : Γ ⊢[PRAAx]
    dispatch s t u ≐ s := (sel_zero (eqb_of_ne hs)).eqTrans (sel_one (eqb_of_eq ht))

theorem dispatch_same (s t u : PTm n) (hs : Γ ⊢[PRAAx] neg (s ≐ zero)) (ht : Γ ⊢[PRAAx] neg (t ≐ zero))
    (hst : Γ ⊢[PRAAx] s ≐ t) : Γ ⊢[PRAAx] dispatch s t u ≐ s :=
  (sel_zero (eqb_of_ne hs)).eqTrans ((sel_zero (eqb_of_ne ht)).eqTrans (sel_one (eqb_of_eq hst)))

theorem dispatch_opposite (s t u : PTm n) (hs : Γ ⊢[PRAAx] neg (s ≐ zero)) (ht : Γ ⊢[PRAAx] neg (t ≐ zero))
    (hst : Γ ⊢[PRAAx] neg (s ≐ t)) : Γ ⊢[PRAAx] dispatch s t u ≐ tagProduct s u :=
  (sel_zero (eqb_of_ne hs)).eqTrans ((sel_zero (eqb_of_ne ht)).eqTrans (sel_zero (eqb_of_ne hst)))

theorem read_operand_congr (h B S A E : PTm n) (hA : Γ ⊢[PRAAx] A ≐ E) : Γ ⊢[PRAAx]
    read h B S A ≐ read h B S E := by
  simpa [subst_read] using Prf.eqCongr (read (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![h,B,S,A]) (σ' := ![h,B,S,E])
    (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact hA)

theorem tag_product_congr {s s' t t' : PTm n} (hs : Γ ⊢[PRAAx] s ≐ s') (ht : Γ ⊢[PRAAx] t ≐ t') : Γ ⊢[PRAAx]
    tagProduct s t ≐ tagProduct s' t' := by
  simpa [subst_tagProduct] using Prf.eqCongr (tagProduct (var 0) (var 1) : PTm 2)
    (σ := ![s,t]) (σ' := ![s',t']) (fun i => by fin_cases i; exact hs; exact ht)

theorem recipe_a_zero (h B D S A : PTm n) (ha : Γ ⊢[PRAAx] firstTag h B D S A ≐ zero) : Γ ⊢[PRAAx]
    recipe h B D S A ≐ tagProduct (secondTag h B D S A) (read h (budget h B D) S (entry D h)) :=
  (dispatch_a_zero _ _ _ ha).eqTrans (tag_product_congr (.eqRefl _)
    (read_operand_congr h (budget h B D) S _ _ (third_when_a_zero _ _ _ _ _ ha)))

/-- A zero lower sign for a and d gives zero even when b has any sign.
The d test is the actual third query, not a raw radicand-code test. -/
theorem recipe_a_d_zero (h B D S A : PTm n) (ha : Γ ⊢[PRAAx] firstTag h B D S A ≐ zero)
    (hd : Γ ⊢[PRAAx] read h (budget h B D) S (entry D h) ≐ zero) : Γ ⊢[PRAAx]
    recipe h B D S A ≐ zero := (recipe_a_zero h B D S A ha).eqTrans (tag_product_zero_right _ _ hd)

def output (h B D S A : PTm n) : PTm n := pairT (thirdInput h B D S A) (recipe h B D S A)
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (h B D S A : PTm n) : PTm n := PTm.app outputF ![h,B,D,S,A]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (h B D S A : PTm n) :
    Syn.subst σ (output h B D S A) = output (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ S) (Syn.subst σ A) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (h B D S A : PTm n) :
    Syn.subst σ (run h B D S A) = run (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ S) (Syn.subst σ A) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (h B D S A : PTm n) : Γ ⊢[PRAAx] run h B D S A ≐ output h B D S A := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![h,B,D,S,A]
theorem returned_third (h B D S A : PTm n) : Γ ⊢[PRAAx] fstT (run h B D S A) ≐ thirdInput h B D S A :=
  (congrFst (program_at _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_tag (h B D S A : PTm n) : Γ ⊢[PRAAx] sndT (run h B D S A) ≐ recipe h B D S A :=
  (congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_fits (h B D S A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    arrayHeight h (fstT (run h B D S A)) (budget h B D) :=
  QuadraticTowerMultiplicationHeight.array_congr (.eqRefl _) (returned_third _ _ _ _ _).eqSymm (.eqRefl _)
    (third_input_fits h B D S A b hb hD ha)
theorem returned_bound (h B D S A : PTm n) : Γ ⊢[PRAAx] lt (sndT (run h B D S A)) (succ two) :=
  lt_congr (returned_tag _ _ _ _ _).eqSymm (.eqRefl _) (recipe_bound _ _ _ _ _)

theorem actual_sign_norm_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1) ⟶ radicandsHeight (var 2) (succ (var 0)) (var 4) ⟶
      arrayHeight (succ (var 0)) (var 3) (var 4) ⟶
        arrayHeight (var 0) (norm (var 0) (var 1) (var 2) (var 3)) (growth (QuadraticTowerGrowth.path (succ (var 0))) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (norm_height _ _ _ _ (var 4) Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_third_sign_operand_fits_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ radicandsHeight (var 2) (succ (var 0)) (var 5) ⟶
      arrayHeight (succ (var 0)) (var 4) (var 5) ⟶
        arrayHeight (var 0) (thirdInput (var 0) (var 1) (var 2) (var 3) (var 4)) (budget (var 0) (var 1) (var 2))) :=
  closeUniv 6 (.impI (.impI (.impI (third_input_fits _ _ _ _ _ (var 5) Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_three_sign_addresses_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ radicandsHeight (var 2) (succ (var 0)) (var 5) ⟶
      arrayHeight (succ (var 0)) (var 4) (var 5) ⟶
        lt (code (var 0) (leftHalf (var 0) (var 4)) (budget (var 0) (var 1) (var 2))) (horizon (var 0) (budget (var 0) (var 1) (var 2))) ⋏
          (lt (code (var 0) (rightHalf (var 0) (var 4)) (budget (var 0) (var 1) (var 2))) (horizon (var 0) (budget (var 0) (var 1) (var 2))) ⋏
            lt (code (var 0) (thirdInput (var 0) (var 1) (var 2) (var 3) (var 4)) (budget (var 0) (var 1) (var 2)))
              (horizon (var 0) (budget (var 0) (var 1) (var 2))))) :=
  closeUniv 6 (.impI (.impI (.impI (sign_operand_addresses _ _ _ _ _ (var 5) Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_sign_recipe_tag_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (recipe (var 0) (var 1) (var 2) (var 3) (var 4)) (succ two)) := closeUniv 5 (recipe_bound _ _ _ _ _)

theorem actual_zero_a_zero_radicand_recipe_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (firstTag (var 0) (var 1) (var 2) (var 3) (var 4) ≐ zero ⟶
      read (var 0) (budget (var 0) (var 1) (var 2)) (var 3) (entry (var 2) (var 0)) ≐ zero ⟶
        recipe (var 0) (var 1) (var 2) (var 3) (var 4) ≐ zero) :=
  closeUniv 5 (.impI (.impI (recipe_a_d_zero _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_sign_recipe_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)

theorem actual_returned_sign_operand_fits_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ radicandsHeight (var 2) (succ (var 0)) (var 5) ⟶
      arrayHeight (succ (var 0)) (var 4) (var 5) ⟶
        arrayHeight (var 0) (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (budget (var 0) (var 1) (var 2))) :=
  closeUniv 6 (.impI (.impI (.impI (returned_fits _ _ _ _ _ (var 5) Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_returned_sign_tag_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (succ two)) := closeUniv 5 (returned_bound _ _ _ _ _)

end LeanProofs.IPRA.Algebra.QuadraticTowerSignRecipe
