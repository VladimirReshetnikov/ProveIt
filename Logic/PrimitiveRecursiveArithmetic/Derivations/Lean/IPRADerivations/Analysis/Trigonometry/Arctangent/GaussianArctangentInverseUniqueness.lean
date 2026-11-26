import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentNamedInverse
import IPRADerivations.Analysis.RationalArithmetic.GaussianValueNormalizerExtensionality

/-!
# Uniqueness of rational inverse arctangent approximants

The finite lower slope converts a vanishing difference of the original
arctangent observations into a vanishing difference of the selected
rational parameters. The independent value normalizers remove the
diagonal slack at actual finite queries.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentInverseUniqueness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentInverseForward (input)
open GaussianArctangentInverseSampler (index mesh mesh_positive index_le raw rawF raw_at)
open GaussianArctangentNamedChord (imaginary_coordinate_radius)
open GaussianArctangentNamedInverse (modulus forwardSample forward_sample_error raw_regular)
open GaussianArctangentNamedSlope (ordinate)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (regular)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianValueNormalizerExtensionality (rawDiagonal normalized_names_equivalent)
open RationalCubeMidpoint (fraction)
open RationalGaussianEmbedding (embed)
open RationalValueBounds (radius radius_mono radius_symmetric radius_triangle)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem retimed_parameter_radius (p r A B C D H : PTm n) (hpr : Γ ⊢[PRAAx] le p r)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (hA : Γ ⊢[PRAAx] le A B) (hC : Γ ⊢[PRAAx] le C D)
    (h : Γ ⊢[PRAAx] radius (ordinate r A B) (ordinate r C D) H (unit p)) :
    Γ ⊢[PRAAx] radius (fraction A B) (fraction C D) (H+two) (unit p) := by
  let U := unit p
  let V := unit r
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) r
  have hraw := GaussianArctangentInverseGap.inverse_radius r r A B C D H U hB hD hA hC h
  have order := GaussianExponentialReference.unit_monotone hpr
  exact radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hV hV) hU) hraw
    (by dsimp only [U,V]; ipra_le 2*𝔞 (unit r)*𝔞 (unit p)*sl order)

theorem retimed_parameter_distance (p r A B C D H : PTm n) (hpr : Γ ⊢[PRAAx] le p r)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (hA : Γ ⊢[PRAAx] le A B) (hC : Γ ⊢[PRAAx] le C D)
    (h : Γ ⊢[PRAAx] radius (ordinate r A B) (ordinate r C D) H (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (embed (fraction A B)) (embed (fraction C D)) (H+two) (unit p) :=
  RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ (unit_positive p)
    (retimed_parameter_radius p r A B C D H hpr hB hD hA hC h)

theorem same_stage_parameter_radius (p A B C D H : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (hA : Γ ⊢[PRAAx] le A B) (hC : Γ ⊢[PRAAx] le C D)
    (h : Γ ⊢[PRAAx] radius (ordinate p A B) (ordinate p C D) H (unit p)) :
    Γ ⊢[PRAAx] radius (fraction A B) (fraction C D) (H+two) (unit p) :=
  retimed_parameter_radius p p A B C D H (le_refl p) hB hD hA hC h

theorem same_stage_parameter_distance (p A B C D H : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (hA : Γ ⊢[PRAAx] le A B) (hC : Γ ⊢[PRAAx] le C D)
    (h : Γ ⊢[PRAAx] radius (ordinate p A B) (ordinate p C D) H (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (embed (fraction A B)) (embed (fraction C D)) (H+two) (unit p) :=
  retimed_parameter_distance p p A B C D H (le_refl p) hB hD hA hC h

def selectedAt (f a b : PR 2) (p x : PTm n) : Fm PTm n :=
  le one (ap2 b p x) ⋏
    (le (ap2 a p x) (ap2 b p x) ⋏ ap2 f p x ≐ embed (fraction (ap2 a p x) (ap2 b p x)))

def selected (f a b : PR 2) (x : PTm n) : Fm PTm n :=
  .all (selectedAt f a b (var 0) (Syn.shift x))

def forwardAt (a b : PR 2) (p x : PTm n) : PTm n :=
  ordinate p (ap2 a p x) (ap2 b p x)

def forwardDiagonal (a b c d : PR 2) (x y H : PTm n) : Fm PTm n :=
  .all (radius (forwardAt a b (var 0) (Syn.shift x))
    (forwardAt c d (var 0) (Syn.shift y)) (Syn.shift H) (unit (var 0)))

@[simp] theorem subst_selectedAt {m : ℕ} (σ : Fin n → PTm m) (f a b : PR 2) (p x : PTm n) :
    (selectedAt f a b p x).subst σ = selectedAt f a b (Syn.subst σ p) (Syn.subst σ x) := by
  simp [selectedAt]

@[simp] theorem subst_selected {m : ℕ} (σ : Fin n → PTm m) (f a b : PR 2) (x : PTm n) :
    (selected f a b x).subst σ = selected f a b (Syn.subst σ x) := by
  simp [selected,Syn.subst_shift,Syn.shift_subst]

@[simp] theorem subst_forwardAt {m : ℕ} (σ : Fin n → PTm m) (a b : PR 2) (p x : PTm n) :
    Syn.subst σ (forwardAt a b p x) = forwardAt a b (Syn.subst σ p) (Syn.subst σ x) := by
  simp [forwardAt,ordinate]

@[simp] theorem subst_forwardDiagonal {m : ℕ} (σ : Fin n → PTm m) (a b c d : PR 2) (x y H : PTm n) :
    (forwardDiagonal a b c d x y H).subst σ =
      forwardDiagonal a b c d (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ H) := by
  simp [forwardDiagonal,Syn.subst_shift,Syn.shift_subst]

theorem selected_at (f a b : PR 2) (p x : PTm n) (h : Γ ⊢[PRAAx] selected f a b x) :
    Γ ⊢[PRAAx] selectedAt f a b p x := by
  simpa only [selected,subst_selectedAt,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE p

theorem forward_diagonal_at (a b c d : PR 2) (p x y H : PTm n)
    (h : Γ ⊢[PRAAx] forwardDiagonal a b c d x y H) :
    Γ ⊢[PRAAx] radius (forwardAt a b p x) (forwardAt c d p y) H (unit p) := by
  simpa only [forwardDiagonal,RationalValueBounds.subst_radius,subst_forwardAt,GaussianCoefficientNameBounds.subst_unit,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE p

theorem parameter_diagonal (f g a b c d : PR 2) (x y H : PTm n)
    (hf : Γ ⊢[PRAAx] selected f a b x) (hg : Γ ⊢[PRAAx] selected g c d y)
    (h : Γ ⊢[PRAAx] forwardDiagonal a b c d x y H) :
    Γ ⊢[PRAAx] rawDiagonal f g x y (H+two) := by
  refine .allI ?_
  let X := Syn.shift x
  let Y := Syn.shift y
  let K := Syn.shift H
  let p : PTm (n+1) := var 0
  have hs : Γ.map Fm.shift ⊢[PRAAx] selected f a b X := by
    simpa only [Fm.shift,subst_selected,Syn.shift,X] using hf.shift
  have ht : Γ.map Fm.shift ⊢[PRAAx] selected g c d Y := by
    simpa only [Fm.shift,subst_selected,Syn.shift,Y] using hg.shift
  have hr : Γ.map Fm.shift ⊢[PRAAx] forwardDiagonal a b c d X Y K := by
    simpa only [Fm.shift,subst_forwardDiagonal,Syn.shift,X,Y,K] using h.shift
  have sp := selected_at f a b p X hs
  have tp := selected_at g c d p Y ht
  have d := same_stage_parameter_distance p (ap2 a p X) (ap2 b p X) (ap2 c p Y) (ap2 d p Y) K
    sp.andE₁ tp.andE₁ sp.andE₂.andE₁ tp.andE₂.andE₁ (forward_diagonal_at a b c d p X Y K hr)
  simpa only [rawDiagonal,Syn.shift,PTm.subst_add,PTm.subst_succ,PTm.subst_zero,p,X,Y,K] using
    distance_congr sp.andE₂.andE₂.eqSymm tp.andE₂.andE₂.eqSymm (.eqRefl _) (.eqRefl _) d

theorem inverse_of_forward_equivalence (f g a b c d : PR 2) (L M x y H : PTm n)
    (hf : Γ ⊢[PRAAx] regular f L x) (hg : Γ ⊢[PRAAx] regular g M y)
    (hfsel : Γ ⊢[PRAAx] selected f a b x) (hgsel : Γ ⊢[PRAAx] selected g c d y)
    (h : Γ ⊢[PRAAx] forwardDiagonal a b c d x y H) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianFastValueCut.nameF f) (GaussianFastValueCut.nameF g)
      (GaussianFastValueCut.nameData L x) (GaussianFastValueCut.nameData M y) :=
  normalized_names_equivalent f g L M x y (H+two) hf hg (parameter_diagonal f g a b c d x y H hfsel hgsel h)

private theorem original_forward_pair_error (f g : PR 2) (p x y z w : PTm n)
    (hf : Γ ⊢[PRAAx] input f x z) (hg : Γ ⊢[PRAAx] input g y w)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] radius (forwardSample f p p x) (forwardSample g p p y) (num 18) (unit p) := by
  let U := unit p
  let a := forwardSample f p p x
  let b := forwardSample g p p y
  let ux := GaussianArctangentInverseSampler.ordinate f p x
  let uy := GaussianArctangentInverseSampler.ordinate g p y
  have hp := unit_positive (Γ := Γ) p
  have hp₂ := positive_product _ _ hp hp
  have first := forward_sample_error f p p x z hf
  have mid := imaginary_coordinate_radius _ _ _ _ hp₂ (cross_at f g x y p p he)
  have last := radius_symmetric b uy (num 8) U (forward_sample_error g p p y w hg)
  have d := radius_triangle a uy b _ _ (num 8) U
    (radius_triangle a ux uy (num 8) U (U+U) (U*U) first mid) last
  exact radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hp hp₂) hp) d
    (le_of_eq_add (d := zero) (by ipra_ring))

theorem original_raw_inverse_diagonal (f g : PR 2) (x y z w : PTm n)
    (hf : Γ ⊢[PRAAx] input f x z) (hg : Γ ⊢[PRAAx] input g y w)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx] rawDiagonal (rawF f) (rawF g) x y (num 20) := by
  refine .allI ?_
  let X := Syn.shift x
  let Y := Syn.shift y
  let Z := Syn.shift z
  let W := Syn.shift w
  let p : PTm (n+1) := var 0
  have hs : Γ.map Fm.shift ⊢[PRAAx] input f X Z := by
    simpa only [Fm.shift,GaussianArctangentInverseForward.subst_input,Syn.shift,X,Z] using hf.shift
  have ht : Γ.map Fm.shift ⊢[PRAAx] input g Y W := by
    simpa only [Fm.shift,GaussianArctangentInverseForward.subst_input,Syn.shift,Y,W] using hg.shift
  have hr : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent f g X Y := by
    simpa [Fm.shift,Syn.shift,X,Y] using he.shift
  have d := same_stage_parameter_distance p (index f p X) (mesh p) (index g p Y) (mesh p) (num 18)
    (mesh_positive _) (mesh_positive _) (index_le _ _ _) (index_le _ _ _)
    (original_forward_pair_error f g p X Y Z W hs ht hr)
  simpa only [rawDiagonal,Syn.shift,PTm.subst_num,p,X,Y] using
    distance_congr (raw_at f p X).eqSymm (raw_at g p Y).eqSymm (by ipra_ring) (.eqRefl _) d

theorem original_inverse_unique (f g : PR 2) (x y z w : PTm n)
    (hf : Γ ⊢[PRAAx] input f x z) (hg : Γ ⊢[PRAAx] input g y w)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianArctangentNamedInverse.nameF f) (GaussianArctangentNamedInverse.nameF g)
      (GaussianArctangentNamedInverse.data x) (GaussianArctangentNamedInverse.data y) :=
  normalized_names_equivalent _ _ modulus modulus x y (num 20)
    (raw_regular f x z hf) (raw_regular g y w hg) (original_raw_inverse_diagonal f g x y z w hf hg he)

theorem actual_arctangent_inverse_of_forward_equivalence_closed (f g a b c d : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((regular f (var 2) (var 0) ⋏ regular g (var 3) (var 1)) ⟶
        (selected f a b (var 0) ⋏ selected g c d (var 1)) ⟶
        forwardDiagonal a b c d (var 0) (var 1) (var 4) ⟶
        crossEquivalent (GaussianFastValueCut.nameF f) (GaussianFastValueCut.nameF g)
          (GaussianFastValueCut.nameData (var 2) (var 0)) (GaussianFastValueCut.nameData (var 3) (var 1))) :=
  closeUniv 5 (.impI (.impI (.impI (inverse_of_forward_equivalence f g a b c d _ _ _ _ _
    Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

theorem actual_arctangent_inverse_unique_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((input f (var 0) (var 2) ⋏ input g (var 1) (var 3)) ⟶ crossEquivalent f g (var 0) (var 1) ⟶
        crossEquivalent (GaussianArctangentNamedInverse.nameF f) (GaussianArctangentNamedInverse.nameF g)
          (GaussianArctangentNamedInverse.data (var 0)) (GaussianArctangentNamedInverse.data (var 1))) :=
  closeUniv 4 (.impI (.impI (original_inverse_unique f g _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentInverseUniqueness
