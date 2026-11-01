import ZFCinPA.ZFDelta1
import ZFCinPA.Translation
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
import Foundation.FirstOrder.Bootstrapping.FixedPoint

/-!
# The literal uniform sentence `PA ⊢ ∀ n, Prov_ZFC(⌜Conₙ(ZFC)⌝)`

The numeralwise theorem `zfc_proves_conZFCSet` is indexed by a
*metatheoretic* natural number: a Lean `forall` in front of it is not a
single arithmetic sentence.  This module constructs the distinct sentence
requested by the notation

`PA proves: for every n, ZFC proves Conₙ(ZFC)`,

in which the inner "proves" is Foundation's represented `𝗭𝗙𝗖` provability
predicate and the outer quantifier ranges over every element of an arbitrary
model of PA — including nonstandard elements.

The model to mirror is
`BoundedPAConsistency.UniformInternalProvability`, where the `n`-dependence
of the quoted sentence went through `ssnum`, numeral substitution into a
quoted unary template.  `ℒₛₑₜ` has no function symbols, hence no numerals and
no substitution template; the `n`-dependence must instead go through a
represented *code builder*: a `𝚺₁` graph that, inside the model, assembles the
Gödel code of `Conₙ(ZFC)` from `n`.

## The shape of the code

`conZFCSet n` is the `toSet`-image of
`conZFCForm n = sealF (conZFCBodyF n)`, and

* `conZFCBodyF n = fAll⁴ (fImp (fNumF 3 n) restForm)` where `restForm` is a
  fixed (`n`-independent) formula — the only `n`-dependence of the body is
  the numeral formula `fNumF 3 n`;
* `fNumF` satisfies the primitive recursion
  `fNumF 3 0 = fEmptyF 3` and
  `fNumF 3 (m+1) = fEx (fAnd (fNumF 0 m) (fSuccF 4 0))`, with the inner
  chain `fNumF 0 (m+1) = fEx (fAnd (fNumF 0 m) (fSuccF 1 0))`;
* `sealF` prepends `bound (conZFCBodyF n)` universal quantifiers, a count
  that is an explicit affine function of `n`.

The Gödel code of a translated formula depends on the translation depth only
through the rendering of *free* De Bruijn indices, and Foundation's coding of
a bound variable `#i` does not mention the ambient arity.  The
depth-independence lemma below (`quote_toSet_congr`) therefore lets every
layer of the builder work at a convenient fixed depth: the numeral chain at
depth `1`, the antecedent at depth `4`, and `restForm` at depth
`bound restForm` — the last choice discharging its free-variable side
condition by `free_lt_bound` alone, with no structural analysis of the large
derivability formulas inside `restForm`.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping

/-! ## Form-level analysis

Everything in this section is metatheoretic syntax: free-variable supports of
the small numeral macros, the identification of the fixed part `restForm` of
the consistency body, and the affine growth of the sealing count.  No model
appears. -/

section FormLevel

open SetTheory (Form Free bound fEmptyF fSuccF fSetByF fIff)

/-- The fixed (`n`-independent) inner part of `conZFCBodyF`: everything under
the four binders except the numeral antecedent. -/
def restForm : SetTheory.Form :=
  .fImp (BoundedZFCConsistency.fTaggedEmptyF 2 2)
    (.fImp (BoundedZFCConsistency.fCtxZFCAxiomsF 1)
      (.fImp (.fAnd (BoundedZFCConsistency.fDerivesF 0 1 2)
        (BoundedZFCConsistency.fDerAllBoundedF 3 0)) .fBot))

/-- `conZFCBodyF n` is four universal quantifiers over an implication whose
antecedent carries all of the `n`-dependence. -/
theorem conZFCBodyF_eq (n : ℕ) :
    BoundedZFCConsistency.conZFCBodyF n =
      .fAll (.fAll (.fAll (.fAll
        (.fImp (BoundedZFCConsistency.fNumF 3 n) restForm)))) := rfl

/-! ### Free-variable supports of the numeral macros -/

/-- The only free slot of `fEmptyF i` is `i`. -/
theorem free_fEmptyF {i n : ℕ} (h : Free n (fEmptyF i)) : n = i := by
  simp [fEmptyF, Free] at h
  omega

/-- The free slots of `fSuccF i j` are among `{i, j}`. -/
theorem free_fSuccF {i j n : ℕ} (h : Free n (fSuccF i j)) : n = i ∨ n = j := by
  simp [fSuccF, fSetByF, fIff, Free] at h
  omega

/-- The only free slot of the numeral formula `fNumF i k` is `i`: the whole
chain of witnesses below the top slot is existentially bound. -/
theorem free_fNumF {i k n : ℕ} (h : Free n (BoundedZFCConsistency.fNumF i k)) :
    n = i := by
  induction k generalizing i n with
  | zero => exact free_fEmptyF h
  | succ k ih =>
      simp only [BoundedZFCConsistency.fNumF, Free] at h
      rcases h with h | h
      · have := ih h
        omega
      · rcases free_fSuccF h with h | h <;> omega

end FormLevel

/-! ## Depth-independence of the quotation

`toSet k φ` renders a repository index `i` as the Foundation bound variable
`#i` whenever `i < k` and as the free variable `&(i - k)` otherwise.
Foundation's Gödel numbering codes `#i` by `i` alone — the ambient arity `k`
is a typing bound, not part of the code — so as long as every free index of
`φ` lies below both depths, the codes agree.  The statement is at the level
of `Semiformula.toNat` (`= Encodable.encode`), whence quotes into any model
agree by `quote_eq_encode`.

The implication case forces a simultaneous statement for the negation, since
`🡒` is negation-normal-form sugar. -/

section DepthIndependence

open SetTheory (Free)

/-- The code of a translated variable below the depth. -/
theorem toNat_toSetVar {k i : ℕ} (h : i < k) :
    (toSetVar k i).toNat = Nat.pair 0 i + 1 := by
  simp [toSetVar, dif_pos h, Semiterm.toNat]

/-- **Depth-independence of the code.**  If every free index of `φ` lies
below both depths, the codes of the two translations agree, and so do the
codes of their negations.  The negation component keeps the implication case
of the induction closed, since `🡒` is negation-normal-form sugar. -/
theorem toNat_toSet_congr (φ : SetTheory.Form) :
    ∀ k₁ k₂ : ℕ, (∀ i, Free i φ → i < k₁) → (∀ i, Free i φ → i < k₂) →
      (toSet k₁ φ).toNat = (toSet k₂ φ).toNat ∧
      ((toSet k₁ φ).neg).toNat = ((toSet k₂ φ).neg).toNat := by
  induction φ with
  | fMem i j =>
      intro k₁ k₂ h₁ h₂
      have hi₁ : i < k₁ := h₁ i (Or.inl rfl)
      have hj₁ : j < k₁ := h₁ j (Or.inr rfl)
      have hi₂ : i < k₂ := h₂ i (Or.inl rfl)
      have hj₂ : j < k₂ := h₂ j (Or.inr rfl)
      constructor <;>
        simp [toSet, Semiformula.neg, Semiformula.toNat, Matrix.vecToNat,
          Matrix.vecHead, Matrix.vecTail, Semiterm.encode_eq_toNat,
          toNat_toSetVar, hi₁, hj₁, hi₂, hj₂]
  | fEq i j =>
      intro k₁ k₂ h₁ h₂
      have hi₁ : i < k₁ := h₁ i (Or.inl rfl)
      have hj₁ : j < k₁ := h₁ j (Or.inr rfl)
      have hi₂ : i < k₂ := h₂ i (Or.inl rfl)
      have hj₂ : j < k₂ := h₂ j (Or.inr rfl)
      constructor <;>
        simp [toSet, Semiformula.neg, Semiformula.toNat, Matrix.vecToNat,
          Matrix.vecHead, Matrix.vecTail, Semiterm.encode_eq_toNat,
          toNat_toSetVar, hi₁, hj₁, hi₂, hj₂]
  | fBot =>
      intro _ _ _ _
      constructor <;> rfl
  | fImp a b iha ihb =>
      intro k₁ k₂ h₁ h₂
      have ha := iha k₁ k₂ (fun i hi => h₁ i (Or.inl hi)) (fun i hi => h₂ i (Or.inl hi))
      have hb := ihb k₁ k₂ (fun i hi => h₁ i (Or.inr hi)) (fun i hi => h₂ i (Or.inr hi))
      constructor <;>
        simp [toSet, Semiformula.imp_eq, Semiformula.neg_eq, Semiformula.neg,
          Semiformula.neg_neg, Semiformula.toNat,
          ha.1, ha.2, hb.1, hb.2]
  | fAnd a b iha ihb =>
      intro k₁ k₂ h₁ h₂
      have ha := iha k₁ k₂ (fun i hi => h₁ i (Or.inl hi)) (fun i hi => h₂ i (Or.inl hi))
      have hb := ihb k₁ k₂ (fun i hi => h₁ i (Or.inr hi)) (fun i hi => h₂ i (Or.inr hi))
      constructor <;>
        simp [toSet, Semiformula.neg, Semiformula.toNat,
          ha.1, ha.2, hb.1, hb.2]
  | fOr a b iha ihb =>
      intro k₁ k₂ h₁ h₂
      have ha := iha k₁ k₂ (fun i hi => h₁ i (Or.inl hi)) (fun i hi => h₂ i (Or.inl hi))
      have hb := ihb k₁ k₂ (fun i hi => h₁ i (Or.inr hi)) (fun i hi => h₂ i (Or.inr hi))
      constructor <;>
        simp [toSet, Semiformula.neg, Semiformula.toNat,
          ha.1, ha.2, hb.1, hb.2]
  | fAll a ih =>
      intro k₁ k₂ h₁ h₂
      have ha := ih (k₁ + 1) (k₂ + 1)
        (fun i hi => by
          cases i with
          | zero => omega
          | succ m => have := h₁ m hi; omega)
        (fun i hi => by
          cases i with
          | zero => omega
          | succ m => have := h₂ m hi; omega)
      constructor <;>
        simp [toSet, Semiformula.neg, Semiformula.toNat, ha.1, ha.2]
  | fEx a ih =>
      intro k₁ k₂ h₁ h₂
      have ha := ih (k₁ + 1) (k₂ + 1)
        (fun i hi => by
          cases i with
          | zero => omega
          | succ m => have := h₁ m hi; omega)
        (fun i hi => by
          cases i with
          | zero => omega
          | succ m => have := h₂ m hi; omega)
      constructor <;>
        simp [toSet, Semiformula.neg, Semiformula.toNat, ha.1, ha.2]

end DepthIndependence

section QuoteLevel

open SetTheory (Free)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Depth-independence, at the level of quotes into an arbitrary model. -/
theorem quote_toSet_congr {φ : SetTheory.Form} {k₁ k₂ : ℕ}
    (h₁ : ∀ i, Free i φ → i < k₁) (h₂ : ∀ i, Free i φ → i < k₂) :
    (⌜toSet k₁ φ⌝ : V) = ⌜toSet k₂ φ⌝ := by
  rw [Semiformula.quote_eq_encode, Semiformula.quote_eq_encode]
  exact congrArg _ ((toNat_toSet_congr φ k₁ k₂ h₁ h₂).1)

/-- Rewriting the depth argument under a quote.  Stated separately because
the depth occurs in the *type* of the translation, so a plain `rw` cannot
touch it. -/
theorem quote_toSet_depth_cast {k₁ k₂ : ℕ} (h : k₁ = k₂) (φ : SetTheory.Form) :
    (⌜toSet k₁ φ⌝ : V) = ⌜toSet k₂ φ⌝ := by subst h; rfl

/-- Quotation computes through the translated implication: `toSet` renders
`fImp` as Foundation's `🡒`, whose code is the coded implication. -/
theorem quote_toSet_fImp (k : ℕ) (a b : SetTheory.Form) :
    (⌜toSet k (.fImp a b)⌝ : V) =
      Bootstrapping.imp ℒₛₑₜ ⌜toSet k a⌝ ⌜toSet k b⌝ := by
  simp [toSet, Semiformula.quote_def]

end QuoteLevel

/-! ## The sealing count

`sealF` closes `conZFCBodyF n` under `bound (conZFCBodyF n)` universal
quantifiers.  Because `fNumF` grows by a fixed formula (`fSuccF`) at each
step, this count is an explicit affine function of `n` whose coefficients are
the `bound`s of three fixed formulas — kept symbolic throughout: nothing ever
evaluates the (large) `bound restForm`. -/

section SealCount

open SetTheory (Form Free bound fEmptyF fSuccF)

/-- `m`-fold `fAll`, outermost first: the normal form of `closeN`. -/
def fAllIter : ℕ → SetTheory.Form → SetTheory.Form
  | 0, f => f
  | m + 1, f => .fAll (fAllIter m f)

theorem fAllIter_fAll (m : ℕ) (f : Form) :
    fAllIter m (.fAll f) = .fAll (fAllIter m f) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [fAllIter, ih]

/-- `closeN` builds exactly the iterated universal closure. -/
theorem closeN_eq_fAllIter : ∀ (m : ℕ) (f : Form),
    SetTheory.closeN m f = fAllIter m f := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro f
      rw [show SetTheory.closeN (m + 1) f = SetTheory.closeN m (.fAll f) from rfl,
        ih, fAllIter_fAll]
      rfl

/-- The seal of the consistency body, as an iterated closure. -/
theorem conZFCForm_eq_fAllIter (n : ℕ) :
    BoundedZFCConsistency.conZFCForm n =
      fAllIter (bound (BoundedZFCConsistency.conZFCBodyF n))
        (BoundedZFCConsistency.conZFCBodyF n) :=
  closeN_eq_fAllIter _ _

/-- `bound` of the successor formula in the inner chain (slot `1` against the
fresh slot `0`).  Never evaluated. -/
def succFormBound1 : ℕ := bound (fSuccF 1 0)

/-- `bound` of the successor formula at the top slot (slot `4` against the
fresh slot `0`).  Never evaluated. -/
def succFormBound4 : ℕ := bound (fSuccF 4 0)

/-- `bound` of the fixed part of the consistency body.  Never evaluated. -/
def restFormBound : ℕ := bound restForm

theorem bound_fEmptyF (i : ℕ) : bound (fEmptyF i) = i + 3 := by
  simp only [fEmptyF, bound]
  omega

theorem bound_fNumF_chain_succ (k : ℕ) :
    bound (BoundedZFCConsistency.fNumF 0 (k + 1)) =
      bound (BoundedZFCConsistency.fNumF 0 k) + succFormBound1 := rfl

/-- The inner numeral chain's `bound` is affine. -/
theorem bound_fNumF_chain : ∀ k : ℕ,
    bound (BoundedZFCConsistency.fNumF 0 k) = 3 + k * succFormBound1 := by
  intro k
  induction k with
  | zero =>
      have h : bound (BoundedZFCConsistency.fNumF 0 0) = 0 + 3 := bound_fEmptyF 0
      omega
  | succ k ih =>
      rw [bound_fNumF_chain_succ, ih, Nat.succ_mul]
      omega

theorem bound_fNumF_three_succ (k : ℕ) :
    bound (BoundedZFCConsistency.fNumF 3 (k + 1)) =
      bound (BoundedZFCConsistency.fNumF 0 k) + succFormBound4 := rfl

/-- The number of quantifiers `sealF` prepends to `conZFCBodyF n`. -/
def sealCount (n : ℕ) : ℕ := bound (BoundedZFCConsistency.conZFCBodyF n)

theorem sealCount_eq (n : ℕ) :
    sealCount n = bound (BoundedZFCConsistency.fNumF 3 n) + restFormBound := rfl

theorem sealCount_zero : sealCount 0 = 6 + restFormBound := by
  have h : bound (BoundedZFCConsistency.fNumF 3 0) = 3 + 3 := bound_fEmptyF 3
  rw [sealCount_eq, h]

theorem sealCount_succ (m : ℕ) :
    sealCount (m + 1) = (3 + m * succFormBound1 + succFormBound4) + restFormBound := by
  rw [sealCount_eq, bound_fNumF_three_succ, bound_fNumF_chain]

/-- `restForm`'s free indices are all below its own `bound` — the only
free-variable fact the construction needs about the large fixed formula, and
it is supplied by the generic `free_lt_bound` with no structural analysis. -/
theorem free_restForm_lt {i : ℕ} (h : Free i restForm) : i < restFormBound :=
  SetTheory.free_lt_bound restForm i h

/-- The consistency body has no free variables: its four binders capture
slots `0`–`3`, the numeral antecedent only uses slot `3`, and every free
index of `restForm` is below `restFormBound ≤ bound (conZFCBodyF n)`…  in
fact the direct argument via `free_fNumF` and `free_lt_bound` needs no
comparison at all: sentencehood is `sentence_conZFCForm`'s job, and this
lemma is about the *body*, used to move its translation depth around. -/
theorem free_conZFCBodyF_lt {n i : ℕ}
    (h : Free i (BoundedZFCConsistency.conZFCBodyF n)) : i + 4 < sealCount n + 4 := by
  rw [conZFCBodyF_eq] at h
  have h4 : Free (i + 4) (Form.fImp (BoundedZFCConsistency.fNumF 3 n) restForm) := h
  have hlt : i + 4 < sealCount n := by
    rcases h4 with h4 | h4
    · have := free_fNumF h4
      omega
    · have h5 := free_restForm_lt h4
      rw [sealCount_eq]
      omega
  omega

end SealCount

/-! ## Quotation of the sealed sentence -/

section QuoteAssembly

open SetTheory (Form Free bound)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `m`-fold coded universal quantifier, outermost first. -/
noncomputable def qqAllIter : ℕ → V → V
  | 0, c => c
  | m + 1, c => ^∀ (qqAllIter m c)

/-- Quotation computes through the iterated closure: the code of the
translation of `fAllIter m f` is `m` coded quantifiers around the code of
`f`'s translation at depth `k + m`. -/
theorem quote_toSet_fAllIter (f : Form) :
    ∀ (m k : ℕ), (⌜toSet k (fAllIter m f)⌝ : V) = qqAllIter m (⌜toSet (k + m) f⌝ : V) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro k
      have h1 : (⌜toSet k (fAllIter (m + 1) f)⌝ : V) =
          ^∀ (⌜toSet (k + 1) (fAllIter m f)⌝ : V) := by
        simp [fAllIter, toSet]
      rw [h1, ih (k + 1),
        quote_toSet_depth_cast (V := V) (show k + 1 + m = k + (m + 1) by omega) f]
      rfl

/-- The translation of a `Form` with free indices below the depth has no
Foundation free variables: every repository index is rendered as a bound
variable `#i`. -/
theorem freeVariables_toSet (φ : Form) :
    ∀ k : ℕ, (∀ i, Free i φ → i < k) → (toSet k φ).freeVariables = ∅ := by
  induction φ with
  | fMem i j =>
      intro k h
      have hi : i < k := h i (Or.inl rfl)
      have hj : j < k := h j (Or.inr rfl)
      simp only [toSet, toSetVar, dif_pos hi, dif_pos hj,
        Semiformula.freeVariables_rel]
      ext x
      simp [Finset.mem_biUnion, Fin.exists_fin_two]
  | fEq i j =>
      intro k h
      have hi : i < k := h i (Or.inl rfl)
      have hj : j < k := h j (Or.inr rfl)
      simp only [toSet, toSetVar, dif_pos hi, dif_pos hj,
        Semiformula.freeVariables_rel]
      ext x
      simp [Finset.mem_biUnion, Fin.exists_fin_two]
  | fBot => intro k _; rfl
  | fImp a b iha ihb =>
      intro k h
      simp [toSet, iha k (fun i hi => h i (Or.inl hi)),
        ihb k (fun i hi => h i (Or.inr hi))]
  | fAnd a b iha ihb =>
      intro k h
      simp [toSet, iha k (fun i hi => h i (Or.inl hi)),
        ihb k (fun i hi => h i (Or.inr hi))]
  | fOr a b iha ihb =>
      intro k h
      simp [toSet, iha k (fun i hi => h i (Or.inl hi)),
        ihb k (fun i hi => h i (Or.inr hi))]
  | fAll a ih =>
      intro k h
      have := ih (k + 1) (fun i hi => by
        cases i with
        | zero => omega
        | succ m => have := h m hi; omega)
      simp [toSet, this]
  | fEx a ih =>
      intro k h
      have := ih (k + 1) (fun i hi => by
        cases i with
        | zero => omega
        | succ m => have := h m hi; omega)
      simp [toSet, this]

/- `conZFCForm n` unfolds to the sealed closure of a large body; nothing
below needs to see through it, and the elaborator must not try.  (Same guard
as in `ZFCinPA.Translation`.) -/
attribute [local irreducible] BoundedZFCConsistency.conZFCForm SetTheory.sealF

set_option maxRecDepth 8000 in
/-- The universal closure in `conZFCSet` is vacuous at the level of codes:
`conZFCForm n` is a closed `Form` (`sentence_conZFCForm`), so its translation
has no free variables and `univCl` is the identity up to the
sentence/proposition embedding, which quotation ignores. -/
theorem quote_conZFCSet (n : ℕ) :
    (⌜conZFCSet n⌝ : V) = ⌜toSet 0 (BoundedZFCConsistency.conZFCForm n)⌝ := by
  have hfv : (toSet 0 (BoundedZFCConsistency.conZFCForm n)).freeVariables = ∅ :=
    freeVariables_toSet _ 0
      (fun i hi => absurd hi (BoundedZFCConsistency.sentence_conZFCForm n i))
  have h2 : ((toSet 0 (BoundedZFCConsistency.conZFCForm n)).univCl :
      SetTheorySemiproposition 0) = toSet 0 (BoundedZFCConsistency.conZFCForm n) := by
    rw [Semiformula.coe_univCl_eq_univCl', Semiformula.univCl'_eq_self_of _ hfv]
  show (⌜((toSet 0 (BoundedZFCConsistency.conZFCForm n)).univCl :
      SetTheorySentence)⌝ : V) = _
  rw [Sentence.quote_def, h2]

end QuoteAssembly

/-! ## The fixed codes

The `n`-independent ingredients of the builder, as standard natural-number
codes.  Working with `Semiformula.toNat` (definitionally `Encodable.encode`)
keeps the constants computable `ℕ`s; `coe_toNat_eq_quote` re-reads each of
them as the corresponding quotation in any model. -/

section FixedCodes

/-- Code of the inner numeral chain's base `fNumF 0 0` at depth `1`. -/
def numChainZeroCode : ℕ := (toSet 1 (BoundedZFCConsistency.fNumF 0 0)).toNat

/-- Code of the inner chain's step formula `fSuccF 1 0` at depth `2`. -/
def numChainStepCode : ℕ := (toSet 2 (SetTheory.fSuccF 1 0)).toNat

/-- Code of the top numeral formula's base `fNumF 3 0` at depth `4`. -/
def conNumZeroCode : ℕ := (toSet 4 (BoundedZFCConsistency.fNumF 3 0)).toNat

/-- Code of the top step formula `fSuccF 4 0` at depth `5`. -/
def conNumStepCode : ℕ := (toSet 5 (SetTheory.fSuccF 4 0)).toNat

/-- Code of the fixed part of the body, at the depth that makes its own
`bound` the free-variable cutoff. -/
def restFormCode : ℕ := (toSet restFormBound restForm).toNat

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A standard code, cast into the model, is the quotation there. -/
theorem coe_toNat_eq_quote {k : ℕ} (φ : SetTheorySemiproposition k) :
    ((φ.toNat : ℕ) : V) = ⌜φ⌝ :=
  (Semiformula.quote_eq_encode φ).symm

end FixedCodes

/-! ## The internal builder

Three primitive recursions on the model (Foundation's `PR` machinery over
`𝗜𝚺₁`), assembled into one `𝚺₁`-defined function:

* `numChainCode x` — the code of the inner von Neumann numeral chain
  (`fNumF 0 ·` at depth `1`);
* `conNumCode x` — the code of the top numeral formula (`fNumF 3 ·` at depth
  `4`), whose successor step consumes `numChainCode` of the *index*, not of
  the previous value;
* `sealCountV x` — the number of sealing quantifiers, the affine function of
  the previous section;
* `allClosure c k` — `k`-fold coded universal quantification, the internal
  counterpart of `qqAllIter`.

Totality at every (possibly nonstandard) `x : V` is exactly what the `PR`
construction's `𝚺₁` induction provides. -/

section InternalBuilder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The inner numeral chain -/

namespace NumChain

noncomputable def blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. y = ↑numChainZeroCode”
  succ := .mkSigma “y ih k. ∃ a, !qqAndDef a ih ↑numChainStepCode ∧ !qqExsDef y a”

noncomputable def construction : PR.Construction V blueprint where
  zero _ := ↑numChainZeroCode
  succ _ _ ih := ^∃ (ih ^⋏ ↑numChainStepCode)
  zero_defined := .mk fun v ↦ by simp [blueprint, numeral_eq_natCast]
  succ_defined := .mk fun v ↦ by simp [blueprint, numeral_eq_natCast]

end NumChain

/-- The code of `toSet 1 (fNumF 0 x)`, extended to every model element by
primitive recursion. -/
noncomputable def numChainCode (x : V) : V := NumChain.construction.result ![] x

/-- Graph of `numChainCode`. -/
noncomputable def numChainGraph : 𝚺₁.Semisentence 2 := NumChain.blueprint.resultDef

@[simp] lemma numChainCode_zero : numChainCode (0 : V) = ↑numChainZeroCode := by
  simp [numChainCode, NumChain.construction]

@[simp] lemma numChainCode_succ (x : V) :
    numChainCode (x + 1) = ^∃ (numChainCode x ^⋏ ↑numChainStepCode) := by
  simp [numChainCode, NumChain.construction]

instance numChainCode.defined :
    𝚺₁-Function₁ (numChainCode : V → V) via numChainGraph := .mk fun v ↦ by
  simpa [numChainGraph, numChainCode, Matrix.empty_eq] using
    NumChain.construction.result_defined_iff v

/-! ### The top numeral formula -/

namespace ConNum

noncomputable def blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. y = ↑conNumZeroCode”
  succ := .mkSigma
    “y ih k. ∃ g, !numChainGraph g k ∧ ∃ a, !qqAndDef a g ↑conNumStepCode ∧ !qqExsDef y a”

noncomputable def construction : PR.Construction V blueprint where
  zero _ := ↑conNumZeroCode
  succ _ k _ := ^∃ (numChainCode k ^⋏ ↑conNumStepCode)
  zero_defined := .mk fun v ↦ by simp [blueprint, numeral_eq_natCast]
  succ_defined := .mk fun v ↦ by simp [blueprint, numeral_eq_natCast]

end ConNum

/-- The code of `toSet 4 (fNumF 3 x)`, extended to every model element.  Its
successor step reads the numeral chain at the *index*, mirroring
`fNumF 3 (m+1) = fEx (fAnd (fNumF 0 m) (fSuccF 4 0))`. -/
noncomputable def conNumCode (x : V) : V := ConNum.construction.result ![] x

/-- Graph of `conNumCode`. -/
noncomputable def conNumGraph : 𝚺₁.Semisentence 2 := ConNum.blueprint.resultDef

@[simp] lemma conNumCode_zero : conNumCode (0 : V) = ↑conNumZeroCode := by
  simp [conNumCode, ConNum.construction]

@[simp] lemma conNumCode_succ (x : V) :
    conNumCode (x + 1) = ^∃ (numChainCode x ^⋏ ↑conNumStepCode) := by
  simp [conNumCode, ConNum.construction]

instance conNumCode.defined :
    𝚺₁-Function₁ (conNumCode : V → V) via conNumGraph := .mk fun v ↦ by
  simpa [conNumGraph, conNumCode, Matrix.empty_eq] using
    ConNum.construction.result_defined_iff v

/-! ### The sealing count, internally -/

namespace SealCount

noncomputable def blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. y = ↑(6 + restFormBound)”
  succ := .mkSigma
    “y ih k. y = ↑(3 + succFormBound4 + restFormBound) + k * ↑succFormBound1”

noncomputable def construction : PR.Construction V blueprint where
  zero _ := ↑(6 + restFormBound)
  succ _ k _ := ↑(3 + succFormBound4 + restFormBound) + k * ↑succFormBound1
  zero_defined := .mk fun v ↦ by simp [blueprint, numeral_eq_natCast]
  succ_defined := .mk fun v ↦ by simp [blueprint, numeral_eq_natCast]

end SealCount

/-- The number of quantifiers the seal prepends, as a function of the model
element — the internal counterpart of `sealCount`. -/
noncomputable def sealCountV (x : V) : V := SealCount.construction.result ![] x

/-- Graph of `sealCountV`. -/
noncomputable def sealCountGraph : 𝚺₁.Semisentence 2 := SealCount.blueprint.resultDef

@[simp] lemma sealCountV_zero : sealCountV (0 : V) = ↑(6 + restFormBound) := by
  simp [sealCountV, SealCount.construction]

@[simp] lemma sealCountV_succ (x : V) :
    sealCountV (x + 1) =
      ↑(3 + succFormBound4 + restFormBound) + x * ↑succFormBound1 := by
  simp [sealCountV, SealCount.construction]

instance sealCountV.defined :
    𝚺₁-Function₁ (sealCountV : V → V) via sealCountGraph := .mk fun v ↦ by
  simpa [sealCountGraph, sealCountV, Matrix.empty_eq] using
    SealCount.construction.result_defined_iff v

/-! ### Iterated coded universal quantification -/

namespace AllClosure

noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y c. y = c”
  succ := .mkSigma “y ih k c. !qqAllDef y ih”

noncomputable def construction : PR.Construction V blueprint where
  zero v := v 0
  succ _ _ ih := ^∀ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

end AllClosure

/-- `allClosure c k = ^∀ ⋯ ^∀ c` (`k` coded quantifiers), for every model
element `k`. -/
noncomputable def allClosure (c k : V) : V := AllClosure.construction.result ![c] k

/-- Graph of `allClosure`, argument order `(value, base, count)`. -/
noncomputable def allClosureGraph : 𝚺₁.Semisentence 3 :=
  AllClosure.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

@[simp] lemma allClosure_zero (c : V) : allClosure c 0 = c := by
  simp [allClosure, AllClosure.construction]

@[simp] lemma allClosure_succ (c k : V) :
    allClosure c (k + 1) = ^∀ (allClosure c k) := by
  simp [allClosure, AllClosure.construction]

instance allClosure.defined :
    𝚺₁-Function₂ (allClosure : V → V → V) via allClosureGraph := .mk fun v ↦ by
  simp [AllClosure.construction.result_defined_iff, allClosureGraph, allClosure,
    Matrix.constant_eq_singleton]

end InternalBuilder

/-! ## Standard points of the builder layers

At a standard element `↑m` each layer computes exactly the quotation of the
corresponding syntactic object.  All proofs are external inductions on `m`
driven by the layers' defining equations, the quotation equations of the
translation, and depth-independence. -/

section StandardPoints

open SetTheory (Free)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private lemma free_fNumF_lt {j k i m : ℕ} (hjk : j < k)
    (h : Free i (BoundedZFCConsistency.fNumF j m)) : i < k := by
  have := free_fNumF h
  omega

/-- The inner chain agrees with the quotation of `fNumF 0 ·` at depth `1`. -/
theorem numChainCode_natCast (m : ℕ) :
    numChainCode ((m : ℕ) : V) = ⌜toSet 1 (BoundedZFCConsistency.fNumF 0 m)⌝ := by
  induction m with
  | zero =>
      rw [Nat.cast_zero, numChainCode_zero]
      exact coe_toNat_eq_quote _
  | succ m ih =>
      rw [Nat.cast_succ, numChainCode_succ, ih]
      have hq : (⌜toSet 1 (BoundedZFCConsistency.fNumF 0 (m + 1))⌝ : V) =
          ^∃ ((⌜toSet 2 (BoundedZFCConsistency.fNumF 0 m)⌝ : V) ^⋏
            (⌜toSet 2 (SetTheory.fSuccF 1 0)⌝ : V)) := by
        simp [BoundedZFCConsistency.fNumF, toSet]
      rw [hq]
      simp only [qqExs_inj, qqAnd_inj]
      constructor
      · exact quote_toSet_congr (fun i => free_fNumF_lt Nat.one_pos)
          (fun i => free_fNumF_lt (by omega))
      · have := coe_toNat_eq_quote (V := V) (toSet 2 (SetTheory.fSuccF 1 0))
        simpa [numChainStepCode] using this

/-- The top numeral formula agrees with the quotation of `fNumF 3 ·` at
depth `4`. -/
theorem conNumCode_natCast (m : ℕ) :
    conNumCode ((m : ℕ) : V) = ⌜toSet 4 (BoundedZFCConsistency.fNumF 3 m)⌝ := by
  cases m with
  | zero =>
      rw [Nat.cast_zero, conNumCode_zero]
      exact coe_toNat_eq_quote _
  | succ m =>
      rw [Nat.cast_succ, conNumCode_succ, numChainCode_natCast]
      have hq : (⌜toSet 4 (BoundedZFCConsistency.fNumF 3 (m + 1))⌝ : V) =
          ^∃ ((⌜toSet 5 (BoundedZFCConsistency.fNumF 0 m)⌝ : V) ^⋏
            (⌜toSet 5 (SetTheory.fSuccF 4 0)⌝ : V)) := by
        simp [BoundedZFCConsistency.fNumF, toSet]
      rw [hq]
      simp only [qqExs_inj, qqAnd_inj]
      constructor
      · exact quote_toSet_congr (fun i => free_fNumF_lt Nat.one_pos)
          (fun i => free_fNumF_lt (by omega))
      · have := coe_toNat_eq_quote (V := V) (toSet 5 (SetTheory.fSuccF 4 0))
        simpa [conNumStepCode] using this

/-- The internal count agrees with the external sealing count. -/
theorem sealCountV_natCast (m : ℕ) :
    sealCountV ((m : ℕ) : V) = ((sealCount m : ℕ) : V) := by
  cases m with
  | zero => rw [Nat.cast_zero, sealCountV_zero, sealCount_zero]
  | succ m =>
      rw [Nat.cast_succ, sealCountV_succ, sealCount_succ]
      push_cast
      simp [add_comm, add_left_comm]

/-- The internal quantifier iteration agrees with the external one at
standard counts. -/
theorem allClosure_natCast (c : V) (m : ℕ) :
    allClosure c ((m : ℕ) : V) = qqAllIter m c := by
  induction m with
  | zero => rw [Nat.cast_zero, allClosure_zero]; rfl
  | succ m ih => rw [Nat.cast_succ, allClosure_succ, ih]; rfl

end StandardPoints

/-! ## The assembled code builder -/

section CodeBuilder

open SetTheory (Free bound)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The code of the (unsealed) consistency body at model element `x`: four
coded universal quantifiers over the coded implication from the internal
numeral formula to the fixed rest. -/
noncomputable def conZFCBodyCode (x : V) : V :=
  ^∀ (^∀ (^∀ (^∀ (Bootstrapping.imp ℒₛₑₜ (conNumCode x) ↑restFormCode))))

/-- At a standard point the body code is the quotation of the body's
translation at the sealing depth.  Depth-independence moves the antecedent
from depth `4` and the fixed rest from depth `restFormBound` to the ambient
depth `sealCount m + 4`; for the rest, the free-variable side condition is
exactly `free_lt_bound`. -/
theorem conZFCBodyCode_natCast (m : ℕ) :
    conZFCBodyCode ((m : ℕ) : V) =
      ⌜toSet (sealCount m) (BoundedZFCConsistency.conZFCBodyF m)⌝ := by
  have hle : restFormBound ≤ sealCount m := by
    rw [sealCount_eq]
    omega
  have hrest : (⌜toSet (sealCount m + 4) restForm⌝ : V) =
      ⌜toSet restFormBound restForm⌝ :=
    quote_toSet_congr
      (fun i hi => by have := free_restForm_lt hi; omega)
      (fun i hi => free_restForm_lt hi)
  have hnum : (⌜toSet (sealCount m + 4) (BoundedZFCConsistency.fNumF 3 m)⌝ : V) =
      ⌜toSet 4 (BoundedZFCConsistency.fNumF 3 m)⌝ :=
    quote_toSet_congr
      (fun i => free_fNumF_lt (by omega))
      (fun i => free_fNumF_lt (by omega))
  have hbody : (⌜toSet (sealCount m) (BoundedZFCConsistency.conZFCBodyF m)⌝ : V) =
      ^∀ (^∀ (^∀ (^∀ ((⌜toSet (sealCount m + 4)
          (SetTheory.Form.fImp (BoundedZFCConsistency.fNumF 3 m) restForm)⌝ : V))))) := by
    rw [conZFCBodyF_eq]
    simp [toSet]
  rw [hbody, quote_toSet_fImp, hrest, hnum, conZFCBodyCode,
    conNumCode_natCast]
  have hcode : ((restFormCode : ℕ) : V) = ⌜toSet restFormBound restForm⌝ :=
    coe_toNat_eq_quote _
  rw [hcode]

/-- **The internal code builder**: the function whose value at `x` is,
internally, the code of `Conₓ(ZFC)`'s translation. -/
noncomputable def conZFCSetCodeFun (x : V) : V :=
  allClosure (conZFCBodyCode x) (sealCountV x)

/-- **The `𝚺₁` graph of the code builder**, with variable order
`(code, index)`.  It composes the graphs of the layers. -/
noncomputable def conZFCSetCodeGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “c x. ∃ nv, !conNumGraph nv x ∧
        ∃ b, !(Bootstrapping.impGraph ℒₛₑₜ) b nv ↑restFormCode ∧
        ∃ a₁, !qqAllDef a₁ b ∧ ∃ a₂, !qqAllDef a₂ a₁ ∧
        ∃ a₃, !qqAllDef a₃ a₂ ∧ ∃ a₄, !qqAllDef a₄ a₃ ∧
        ∃ k, !sealCountGraph k x ∧ !allClosureGraph c a₄ k”

instance conZFCSetCodeFun.defined :
    𝚺₁-Function₁ (conZFCSetCodeFun : V → V) via conZFCSetCodeGraph := .mk fun v ↦ by
  simp [conZFCSetCodeGraph, conZFCSetCodeFun, conZFCBodyCode, numeral_eq_natCast]

end CodeBuilder

/-! ## The functional relation `ConZFCSetCode` -/

section CodeRelation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The internal code relation**: `c` is the code the builder assigns to
the (possibly nonstandard) index `x`.  Being the graph of a function, it is
total and single-valued by construction; the substantive facts are its `𝚺₁`
definedness (`conZFCSetCodeFun.defined`) and its standard points
(`conZFCSetCode_quote_numeral`). -/
def ConZFCSetCode (c x : V) : Prop := c = conZFCSetCodeFun x

/-- The `𝚺₁` graph means the relation, in every model. -/
theorem eval_conZFCSetCodeGraph_iff {c x : V} :
    conZFCSetCodeGraph.val.Evalb ![c, x] ↔ ConZFCSetCode c x := by
  simp [ConZFCSetCode]

/-- Totality of the code builder at every model element, including
nonstandard ones — this is where the `𝚺₁` induction inside `V` (packaged in
Foundation's `PR` constructions) is consumed. -/
theorem conZFCSetCode_total (x : V) : ∃ c : V, ConZFCSetCode c x :=
  ⟨conZFCSetCodeFun x, rfl⟩

/-- Single-valuedness of the code builder. -/
theorem conZFCSetCode_functional {c₁ c₂ x : V}
    (h₁ : ConZFCSetCode c₁ x) (h₂ : ConZFCSetCode c₂ x) : c₁ = c₂ :=
  h₁.trans h₂.symm

/-- Totality and single-valuedness, packaged. -/
theorem conZFCSetCode_existsUnique (x : V) : ∃! c : V, ConZFCSetCode c x :=
  ⟨conZFCSetCodeFun x, rfl, fun _ h => h⟩

/-- **Quotation agreement at standard points**: at the cast of an external
`n`, the builder computes exactly the quotation of `Conₙ(ZFC)`'s
translation. -/
theorem conZFCSetCodeFun_natCast (n : ℕ) :
    conZFCSetCodeFun ((n : ℕ) : V) = ⌜conZFCSet n⌝ := by
  have h1 : conZFCSetCodeFun ((n : ℕ) : V) =
      qqAllIter (sealCount n)
        (⌜toSet (sealCount n) (BoundedZFCConsistency.conZFCBodyF n)⌝ : V) := by
    rw [conZFCSetCodeFun, sealCountV_natCast, conZFCBodyCode_natCast,
      allClosure_natCast]
  have h2 : (⌜conZFCSet n⌝ : V) =
      qqAllIter (sealCount n)
        (⌜toSet (0 + sealCount n) (BoundedZFCConsistency.conZFCBodyF n)⌝ : V) := by
    rw [quote_conZFCSet, conZFCForm_eq_fAllIter]
    exact quote_toSet_fAllIter _ _ 0
  rw [h1, h2, quote_toSet_depth_cast (V := V)
    (show 0 + sealCount n = sealCount n by omega)]

/-- The standard-point agreement, phrased on the numeral. -/
theorem conZFCSetCode_quote_numeral (n : ℕ) :
    ConZFCSetCode (⌜conZFCSet n⌝ : V) (ORingStructure.numeral n) := by
  show (⌜conZFCSet n⌝ : V) = conZFCSetCodeFun (ORingStructure.numeral n)
  rw [numeral_eq_natCast, conZFCSetCodeFun_natCast]

end CodeRelation

/-! ## The literal sentence -/

/-- The literal object-language reading of
`for every n, ZFC proves Conₙ(ZFC)`: an arithmetic sentence whose universal
quantifier is internal.  The existentially quantified `c` is the code the
builder assigns to `x`; functionality of the builder makes this equivalent to
applying the represented `𝗭𝗙𝗖` provability predicate to that code
directly. -/
noncomputable def paUniformZFCProvabilitySentence : ArithmeticSentence :=
  “∀ x, ∃ c, !conZFCSetCodeGraph c x ∧ !(provable 𝗭𝗙𝗖) c”

section Semantics

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Semantic specification of the literal uniform sentence.  Notice that `x`
has type `V`, so this includes nonstandard indices in nonstandard models. -/
@[simp] theorem eval_paUniformZFCProvabilitySentence_iff :
    paUniformZFCProvabilitySentence.Evalb (M := V) ![] ↔
      ∀ x : V, ∃ c : V, ConZFCSetCode c x ∧ Provable 𝗭𝗙𝗖 c := by
  simp [paUniformZFCProvabilitySentence, ConZFCSetCode]

/-- Through single-valuedness of the builder: the sentence says that every
model element's Con-code is internally `𝗭𝗙𝗖`-provable. -/
theorem eval_paUniformZFCProvabilitySentence_iff_fun :
    paUniformZFCProvabilitySentence.Evalb (M := V) ![] ↔
      ∀ x : V, Provable 𝗭𝗙𝗖 (conZFCSetCodeFun x) := by
  rw [eval_paUniformZFCProvabilitySentence_iff]
  constructor
  · intro h x
    rcases h x with ⟨c, hc, hp⟩
    rwa [show c = conZFCSetCodeFun x from hc] at hp
  · intro h x
    exact ⟨conZFCSetCodeFun x, rfl, h x⟩

/-! ## Standard points -/

/-- **D1 at the standard points.**  For external `n`, the code of
`Conₙ(ZFC)` is internally `𝗭𝗙𝗖`-provable in every model — the numeralwise
theorem `zfc_proves_conZFCSet` pushed inside by Hilbert–Bernays condition
D1.  This is still a metatheoretic family: it deliberately does not quantify
over `V`-elements. -/
theorem provable_conZFCSet_standard_point (n : ℕ) :
    Provable 𝗭𝗙𝗖 (⌜conZFCSet n⌝ : V) :=
  internalize_provability (zfc_proves_conZFCSet n)

/-- Every standard instance of the uniform sentence's matrix holds in every
model: the quotation is the builder's value at the numeral, and it is
provable by D1. -/
theorem paUniformZFCProvability_standard_instance (n : ℕ) :
    ∃ c : V, ConZFCSetCode c (ORingStructure.numeral n) ∧ Provable 𝗭𝗙𝗖 c :=
  ⟨⌜conZFCSet n⌝, conZFCSetCode_quote_numeral n,
    provable_conZFCSet_standard_point n⟩

end Semantics

/-! ## The exact missing uniform selector -/

/-- A model-internal proof selector for the consistency instances.

This name intentionally says `Selector`: unlike the preceding standard-point
theorem, it asks for an internal `𝗭𝗙𝗖`-proof of the built code at *every*
model element, including nonstandard `x`.  Establishing this property
requires a represented recursive constructor for the `𝗭𝗙𝗖`-proofs of the
`conZFCSet` family; the model-theoretic completeness argument behind
`zfc_proves_conZFCSet` does not provide such a constructor. -/
def ZFCProofSelectorIn (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : Prop :=
  ∀ x : V, ∃ c : V, ConZFCSetCode c x ∧ Provable 𝗭𝗙𝗖 c

/-- The selector fact in every PA model.  The explicit `𝗜𝚺₁` instance is
logically redundant (PA supplies it) but makes the model-internal coding
operations' required instance visible in the type. -/
def ZFCProofSelectorInAllModels : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ZFCProofSelectorIn V

section Selector

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The object sentence says exactly that a model-internal selector exists.
This equivalence is definitional packaging; it does not assume or prove the
missing selector. -/
theorem eval_paUniformZFCProvabilitySentence_iff_selector :
    paUniformZFCProvabilitySentence.Evalb (M := V) ![] ↔
      ZFCProofSelectorIn V :=
  eval_paUniformZFCProvabilitySentence_iff

end Selector

/-- Once the represented uniform proof selector has been constructed in
every PA model, first-order completeness yields the requested actual PA
theorem. -/
theorem peano_proves_uniformZFCProvability_of_selectorInAllModels
    (hselector : ZFCProofSelectorInAllModels) :
    Peano ⊢ paUniformZFCProvabilitySentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} Peano _
  intro M _ hPA
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory hPA
  simpa [models_iff] using
    (eval_paUniformZFCProvabilitySentence_iff_selector (V := M)).mpr
      (hselector M)

/-- **Exact characterization of the remaining obligation**: the requested PA
derivation of the uniform internal-provability sentence is equivalent (by
soundness and completeness) to the selector property in every PA model. -/
theorem peano_proves_uniformZFCProvability_iff_selectorInAllModels :
    (Peano ⊢ paUniformZFCProvabilitySentence) ↔ ZFCProofSelectorInAllModels := by
  constructor
  · intro hprov M _ hPA _
    apply (eval_paUniformZFCProvabilitySentence_iff_selector (V := M)).mp
    simpa [models_iff] using (models_of_provable hPA hprov)
  · exact peano_proves_uniformZFCProvability_of_selectorInAllModels
