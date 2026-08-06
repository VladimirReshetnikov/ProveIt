import PolynomialFormulas.SexticComputedResolvents

/-!
# Recursive search for separating sextic resolvents

For a fixed evaluation pair, multiply all ordered nontrivial differences of
the pair- or triple-partition descriptor values.  This collision product is
nonzero exactly when the descriptor values are injective.  It is symmetric in
the six roots, so the certified sparse elementary-symmetric search makes its
integer specialization executable from the sextic coefficients alone.
-/

open scoped BigOperators
open Equiv MvPolynomial

namespace LeanProofs.PolynomialFormulas.SexticSeparatingSearch

open QuinticRadicalPrimrec
open Fin6BlockSystems
open SexticPartitionResolvents
open SexticSeparatingInvariants
open SexticScalarGaloisBridge
open SexticEvaluatedResolvents
open SexticSparseSymmetricSearch
open SexticSparseSymmetricSearch.SparsePolynomial
open SexticComputedResolvents
open SexticRadicalDecidability
open SexticRadicalDecidability.MonicSextic

namespace SparsePolynomial

def productList : List SparsePolynomial → SparsePolynomial
  | [] => const 1
  | p :: ps => mul p (productList ps)

@[simp] theorem toMv_productList (ps : List SparsePolynomial) :
    toMv (productList ps) = (ps.map toMv).prod := by
  induction ps with
  | nil => simp [productList]
  | cons p ps ih => simp [productList, ih]

theorem productList_primrec : Primrec productList := by
  have hstep : Primrec₂ fun _ps : List SparsePolynomial ↦
      fun u : SparsePolynomial × SparsePolynomial ↦ mul u.1 u.2 := by
    change Primrec fun u : List SparsePolynomial ×
        (SparsePolynomial × SparsePolynomial) ↦ mul u.2.1 u.2.2
    exact mul_primrec.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldr Primrec.id (Primrec.const (const 1))
    hstep).of_eq fun ps ↦ by
      induction ps with
      | nil => rfl
      | cons p ps ih =>
          change List.foldr (fun b s ↦ b.mul s) (const 1) ps =
            productList ps at ih
          change p.mul (List.foldr (fun b s ↦ b.mul s) (const 1) ps) =
            p.mul (productList ps)
          rw [ih]

def pairCollisionFactor (x : Fin 2 → ℕ)
    (p q : PairPartition) : SparsePolynomial :=
  if p = q then const 1 else
    sub (pairSparseDescriptorValue x p) (pairSparseDescriptorValue x q)

def tripleCollisionFactor (x : Fin 2 → ℕ)
    (p q : TriplePartition) : SparsePolynomial :=
  if p = q then const 1 else
    sub (tripleSparseDescriptorValue x p) (tripleSparseDescriptorValue x q)

/-- Product of every ordered non-diagonal pair-descriptor difference. -/
def pairSparseCollision (x : Fin 2 → ℕ) : SparsePolynomial :=
  productList (List.ofFn fun p : PairPartition ↦
    productList (List.ofFn fun q : PairPartition ↦
      pairCollisionFactor x p q))

/-- Product of every ordered non-diagonal triple-descriptor difference. -/
def tripleSparseCollision (x : Fin 2 → ℕ) : SparsePolynomial :=
  productList (List.ofFn fun p : TriplePartition ↦
    productList (List.ofFn fun q : TriplePartition ↦
      tripleCollisionFactor x p q))

theorem pairCollisionFactor_primrec (p q : PairPartition) :
    Primrec fun x ↦ pairCollisionFactor x p q := by
  by_cases h : p = q
  · simp only [pairCollisionFactor, h, if_pos]
    exact Primrec.const _
  · simp only [pairCollisionFactor, h, if_neg, sub]
    exact add_primrec.comp (pairSparseDescriptorValue_primrec p)
      (neg_primrec.comp (pairSparseDescriptorValue_primrec q))

theorem tripleCollisionFactor_primrec (p q : TriplePartition) :
    Primrec fun x ↦ tripleCollisionFactor x p q := by
  by_cases h : p = q
  · simp only [tripleCollisionFactor, h, if_pos]
    exact Primrec.const _
  · simp only [tripleCollisionFactor, h, if_neg, sub]
    exact add_primrec.comp (tripleSparseDescriptorValue_primrec p)
      (neg_primrec.comp (tripleSparseDescriptorValue_primrec q))

theorem pairSparseCollision_primrec : Primrec pairSparseCollision := by
  apply productList_primrec.comp
  apply Primrec.list_ofFn
  intro p
  apply productList_primrec.comp
  exact Primrec.list_ofFn fun q ↦ pairCollisionFactor_primrec p q

theorem tripleSparseCollision_primrec : Primrec tripleSparseCollision := by
  apply productList_primrec.comp
  apply Primrec.list_ofFn
  intro p
  apply productList_primrec.comp
  exact Primrec.list_ofFn fun q ↦ tripleCollisionFactor_primrec p q

noncomputable def pairCollisionPolynomial (x : Fin 2 → ℕ) :
    MvPolynomial (Fin 6) ℤ :=
  ∏ p : PairPartition, ∏ q : PairPartition,
    if p = q then 1 else
      pairDescriptorValue x rootVariables p -
        pairDescriptorValue x rootVariables q

noncomputable def tripleCollisionPolynomial (x : Fin 2 → ℕ) :
    MvPolynomial (Fin 6) ℤ :=
  ∏ p : TriplePartition, ∏ q : TriplePartition,
    if p = q then 1 else
      tripleDescriptorValue x rootVariables p -
        tripleDescriptorValue x rootVariables q

theorem pairSparseCollision_toMv (x : Fin 2 → ℕ) :
    toMv (pairSparseCollision x) = pairCollisionPolynomial x := by
  rw [pairSparseCollision, toMv_productList]
  simp only [List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro p hp
  change toMv (productList
      (List.ofFn fun q : PairPartition ↦ pairCollisionFactor x p q)) = _
  rw [toMv_productList]
  simp only [List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro q hq
  change toMv (pairCollisionFactor x p q) = _
  by_cases h : p = q
  · simp [pairCollisionFactor, h]
  · simp only [pairCollisionFactor, h, if_false, toMv_sub]
    rw [← pairDescriptorValue_rootVariables_eq_sparse,
      ← pairDescriptorValue_rootVariables_eq_sparse]
    rfl

theorem tripleSparseCollision_toMv (x : Fin 2 → ℕ) :
    toMv (tripleSparseCollision x) = tripleCollisionPolynomial x := by
  rw [tripleSparseCollision, toMv_productList]
  simp only [List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro p hp
  change toMv (productList
      (List.ofFn fun q : TriplePartition ↦ tripleCollisionFactor x p q)) = _
  rw [toMv_productList]
  simp only [List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro q hq
  change toMv (tripleCollisionFactor x p q) = _
  by_cases h : p = q
  · simp [tripleCollisionFactor, h]
  · simp only [tripleCollisionFactor, h, if_false, toMv_sub]
    rw [← tripleDescriptorValue_rootVariables_eq_sparse,
      ← tripleDescriptorValue_rootVariables_eq_sparse]
    rfl

theorem rename_pairDescriptorValue_rootVariables
    (x : Fin 2 → ℕ) (g : S6) (p : PairPartition) :
    rename g (pairDescriptorValue x rootVariables p) =
      pairDescriptorValue x rootVariables (pairPartitionPerm g p) := by
  change (rename g).toRingHom (pairDescriptorValue x rootVariables p) = _
  rw [map_pairDescriptorValue]
  have hr : (fun i ↦ (rename g).toRingHom (rootVariables i)) =
      fun i ↦ rootVariables (g i) := by
    funext i
    simp [rootVariables]
  rw [hr, pairDescriptorValue_permute]

theorem rename_tripleDescriptorValue_rootVariables
    (x : Fin 2 → ℕ) (g : S6) (p : TriplePartition) :
    rename g (tripleDescriptorValue x rootVariables p) =
      tripleDescriptorValue x rootVariables (triplePartitionPerm g p) := by
  change (rename g).toRingHom (tripleDescriptorValue x rootVariables p) = _
  rw [map_tripleDescriptorValue]
  have hr : (fun i ↦ (rename g).toRingHom (rootVariables i)) =
      fun i ↦ rootVariables (g i) := by
    funext i
    simp [rootVariables]
  rw [hr, tripleDescriptorValue_permute]

theorem pairCollisionPolynomial_rename (x : Fin 2 → ℕ) (g : S6) :
    rename g (pairCollisionPolynomial x) = pairCollisionPolynomial x := by
  simp only [pairCollisionPolynomial, map_prod, apply_ite, map_one, map_sub,
    rename_pairDescriptorValue_rootVariables]
  let e := pairPartitionPerm g
  calc
    (∏ p : PairPartition, ∏ q : PairPartition,
        if p = q then 1 else
          pairDescriptorValue x rootVariables (e p) -
            pairDescriptorValue x rootVariables (e q)) =
      ∏ p : PairPartition, ∏ q : PairPartition,
        if e p = e q then 1 else
          pairDescriptorValue x rootVariables (e p) -
            pairDescriptorValue x rootVariables (e q) := by
        apply Finset.prod_congr rfl
        intro p hp
        apply Finset.prod_congr rfl
        intro q hq
        by_cases hpq : p = q
        · simp [hpq]
        · simp [hpq, e.injective.ne hpq]
    _ = ∏ p : PairPartition, ∏ q : PairPartition,
        if e p = q then 1 else
          pairDescriptorValue x rootVariables (e p) -
            pairDescriptorValue x rootVariables q := by
      apply Finset.prod_congr rfl
      intro p hp
      exact e.prod_comp (fun q ↦
        if e p = q then 1 else
          pairDescriptorValue x rootVariables (e p) -
            pairDescriptorValue x rootVariables q)
    _ = ∏ p : PairPartition, ∏ q : PairPartition,
        if p = q then 1 else
          pairDescriptorValue x rootVariables p -
            pairDescriptorValue x rootVariables q := by
      exact e.prod_comp (fun p ↦ ∏ q : PairPartition,
        if p = q then 1 else
          pairDescriptorValue x rootVariables p -
            pairDescriptorValue x rootVariables q)

theorem tripleCollisionPolynomial_rename (x : Fin 2 → ℕ) (g : S6) :
    rename g (tripleCollisionPolynomial x) = tripleCollisionPolynomial x := by
  simp only [tripleCollisionPolynomial, map_prod, apply_ite, map_one, map_sub,
    rename_tripleDescriptorValue_rootVariables]
  let e := triplePartitionPerm g
  calc
    (∏ p : TriplePartition, ∏ q : TriplePartition,
        if p = q then 1 else
          tripleDescriptorValue x rootVariables (e p) -
            tripleDescriptorValue x rootVariables (e q)) =
      ∏ p : TriplePartition, ∏ q : TriplePartition,
        if e p = e q then 1 else
          tripleDescriptorValue x rootVariables (e p) -
            tripleDescriptorValue x rootVariables (e q) := by
        apply Finset.prod_congr rfl
        intro p hp
        apply Finset.prod_congr rfl
        intro q hq
        by_cases hpq : p = q
        · simp [hpq]
        · simp [hpq, e.injective.ne hpq]
    _ = ∏ p : TriplePartition, ∏ q : TriplePartition,
        if e p = q then 1 else
          tripleDescriptorValue x rootVariables (e p) -
            tripleDescriptorValue x rootVariables q := by
      apply Finset.prod_congr rfl
      intro p hp
      exact e.prod_comp (fun q ↦
        if e p = q then 1 else
          tripleDescriptorValue x rootVariables (e p) -
            tripleDescriptorValue x rootVariables q)
    _ = ∏ p : TriplePartition, ∏ q : TriplePartition,
        if p = q then 1 else
          tripleDescriptorValue x rootVariables p -
            tripleDescriptorValue x rootVariables q := by
      exact e.prod_comp (fun p ↦ ∏ q : TriplePartition,
        if p = q then 1 else
          tripleDescriptorValue x rootVariables p -
            tripleDescriptorValue x rootVariables q)

theorem pairSparseCollision_symmetric (x : Fin 2 → ℕ) :
    (toMv (pairSparseCollision x)).IsSymmetric := by
  intro g
  rw [pairSparseCollision_toMv, pairCollisionPolynomial_rename]

theorem tripleSparseCollision_symmetric (x : Fin 2 → ℕ) :
    (toMv (tripleSparseCollision x)).IsSymmetric := by
  intro g
  rw [tripleSparseCollision_toMv, tripleCollisionPolynomial_rename]

noncomputable def pairCollisionElementary :
    (Fin 2 → ℕ) → SparsePolynomial :=
  elementarySparse pairSparseCollision pairSparseCollision_symmetric

noncomputable def tripleCollisionElementary :
    (Fin 2 → ℕ) → SparsePolynomial :=
  elementarySparse tripleSparseCollision tripleSparseCollision_symmetric

theorem pairCollisionElementary_computable :
    Computable pairCollisionElementary :=
  elementarySparse_computable pairSparseCollision
    pairSparseCollision_primrec.to_comp pairSparseCollision_symmetric

theorem tripleCollisionElementary_computable :
    Computable tripleCollisionElementary :=
  elementarySparse_computable tripleSparseCollision
    tripleSparseCollision_primrec.to_comp tripleSparseCollision_symmetric

theorem pairCollisionElementary_correct (x : Fin 2 → ℕ) :
    MvPolynomial.aeval
        (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
        (toMv (pairCollisionElementary x)) = pairCollisionPolynomial x := by
  rw [pairCollisionElementary, elementarySparse_correct,
    pairSparseCollision_toMv]

theorem tripleCollisionElementary_correct (x : Fin 2 → ℕ) :
    MvPolynomial.aeval
        (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
        (toMv (tripleCollisionElementary x)) = tripleCollisionPolynomial x := by
  rw [tripleCollisionElementary, elementarySparse_correct,
    tripleSparseCollision_toMv]

end SparsePolynomial

/-! ## Integer collision certificates -/

noncomputable def collisionProduct {α K : Type*}
    [Fintype α] [DecidableEq α] [CommRing K] (v : α → K) : K :=
  ∏ p : α, ∏ q : α, if p = q then 1 else v p - v q

theorem collisionProduct_ne_zero_iff {α K : Type*}
    [Fintype α] [DecidableEq α] [CommRing K] [IsDomain K]
    (v : α → K) :
    collisionProduct v ≠ 0 ↔ Function.Injective v := by
  constructor
  · intro h a b hab
    by_contra hne
    apply h
    apply Finset.prod_eq_zero (i := a)
    · exact Finset.mem_univ _
    · apply Finset.prod_eq_zero (i := b)
      · exact Finset.mem_univ _
      · simp [hne, hab]
  · intro hv
    rw [collisionProduct, Finset.prod_ne_zero_iff]
    intro a ha
    rw [Finset.prod_ne_zero_iff]
    intro b hb
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, sub_ne_zero.mpr (hv.ne hab)]

noncomputable def pairCollisionValue
    (a : MonicSextic × (Fin 2 → ℕ)) : ℤ :=
  SparseEvaluation.eval (elementaryValues a.1)
    (SparsePolynomial.pairCollisionElementary a.2)

noncomputable def tripleCollisionValue
    (a : MonicSextic × (Fin 2 → ℕ)) : ℤ :=
  SparseEvaluation.eval (elementaryValues a.1)
    (SparsePolynomial.tripleCollisionElementary a.2)

theorem pairCollisionValue_computable : Computable pairCollisionValue := by
  exact SparseEvaluation.eval_primrec.to_comp.comp
    (elementaryValues_primrec.to_comp.comp Computable.fst)
    (SparsePolynomial.pairCollisionElementary_computable.comp Computable.snd)

theorem tripleCollisionValue_computable : Computable tripleCollisionValue := by
  exact SparseEvaluation.eval_primrec.to_comp.comp
    (elementaryValues_primrec.to_comp.comp Computable.fst)
    (SparsePolynomial.tripleCollisionElementary_computable.comp Computable.snd)

theorem eval_pairDescriptorValue_rootVariables
    {K : Type*} [CommRing K] (x : Fin 2 → ℕ) (r : Fin 6 → K)
    (p : PairPartition) :
    MvPolynomial.eval₂ (Int.castRingHom K) r
        (pairDescriptorValue x rootVariables p) =
      pairDescriptorValue x r p := by
  change (MvPolynomial.eval₂Hom (Int.castRingHom K) r)
      (pairDescriptorValue x rootVariables p) = _
  rw [map_pairDescriptorValue]
  congr 2
  funext i
  simp [rootVariables]

theorem eval_tripleDescriptorValue_rootVariables
    {K : Type*} [CommRing K] (x : Fin 2 → ℕ) (r : Fin 6 → K)
    (p : TriplePartition) :
    MvPolynomial.eval₂ (Int.castRingHom K) r
        (tripleDescriptorValue x rootVariables p) =
      tripleDescriptorValue x r p := by
  change (MvPolynomial.eval₂Hom (Int.castRingHom K) r)
      (tripleDescriptorValue x rootVariables p) = _
  rw [map_tripleDescriptorValue]
  congr 2
  funext i
  simp [rootVariables]

theorem eval_pairCollisionPolynomial
    {K : Type*} [CommRing K] (x : Fin 2 → ℕ) (r : Fin 6 → K) :
    MvPolynomial.eval₂ (Int.castRingHom K) r
        (SparsePolynomial.pairCollisionPolynomial x) =
      collisionProduct (pairDescriptorValue x r) := by
  rw [SparsePolynomial.pairCollisionPolynomial, collisionProduct]
  change (MvPolynomial.eval₂Hom (Int.castRingHom K) r)
      (∏ p : PairPartition, ∏ q : PairPartition,
        if p = q then 1 else
          pairDescriptorValue x rootVariables p -
            pairDescriptorValue x rootVariables q) = _
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  apply Finset.prod_congr rfl
  intro q hq
  by_cases hpq : p = q
  · simp [hpq]
  · simp only [hpq, if_false, map_sub]
    rw [show (MvPolynomial.eval₂Hom (Int.castRingHom K) r)
          (pairDescriptorValue x rootVariables p) =
          pairDescriptorValue x r p by
        exact eval_pairDescriptorValue_rootVariables x r p,
      show (MvPolynomial.eval₂Hom (Int.castRingHom K) r)
          (pairDescriptorValue x rootVariables q) =
          pairDescriptorValue x r q by
        exact eval_pairDescriptorValue_rootVariables x r q]

theorem eval_tripleCollisionPolynomial
    {K : Type*} [CommRing K] (x : Fin 2 → ℕ) (r : Fin 6 → K) :
    MvPolynomial.eval₂ (Int.castRingHom K) r
        (SparsePolynomial.tripleCollisionPolynomial x) =
      collisionProduct (tripleDescriptorValue x r) := by
  rw [SparsePolynomial.tripleCollisionPolynomial, collisionProduct]
  change (MvPolynomial.eval₂Hom (Int.castRingHom K) r)
      (∏ p : TriplePartition, ∏ q : TriplePartition,
        if p = q then 1 else
          tripleDescriptorValue x rootVariables p -
            tripleDescriptorValue x rootVariables q) = _
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  apply Finset.prod_congr rfl
  intro q hq
  by_cases hpq : p = q
  · simp [hpq]
  · simp only [hpq, if_false, map_sub]
    rw [show (MvPolynomial.eval₂Hom (Int.castRingHom K) r)
          (tripleDescriptorValue x rootVariables p) =
          tripleDescriptorValue x r p by
        exact eval_tripleDescriptorValue_rootVariables x r p,
      show (MvPolynomial.eval₂Hom (Int.castRingHom K) r)
          (tripleDescriptorValue x rootVariables q) =
          tripleDescriptorValue x r q by
        exact eval_tripleDescriptorValue_rootVariables x r q]

theorem pairCollisionValue_cast_eq
    {K : Type*} [CommRing K] (f : MonicSextic)
    (x : Fin 2 → ℕ) (r : Fin 6 → K)
    (hesymm : ∀ i : Fin 6,
      MvPolynomial.eval₂ (Int.castRingHom K) r
          (MvPolynomial.esymm (Fin 6) ℤ (i + 1)) =
        (elementaryValues f i : K)) :
    (pairCollisionValue (f, x) : K) =
      collisionProduct (pairDescriptorValue x r) := by
  rw [pairCollisionValue,
    sparse_eval_aeval_esymm (elementaryValues f) r _ hesymm,
    SparsePolynomial.pairCollisionElementary_correct,
    eval_pairCollisionPolynomial]

theorem tripleCollisionValue_cast_eq
    {K : Type*} [CommRing K] (f : MonicSextic)
    (x : Fin 2 → ℕ) (r : Fin 6 → K)
    (hesymm : ∀ i : Fin 6,
      MvPolynomial.eval₂ (Int.castRingHom K) r
          (MvPolynomial.esymm (Fin 6) ℤ (i + 1)) =
        (elementaryValues f i : K)) :
    (tripleCollisionValue (f, x) : K) =
      collisionProduct (tripleDescriptorValue x r) := by
  rw [tripleCollisionValue,
    sparse_eval_aeval_esymm (elementaryValues f) r _ hesymm,
    SparsePolynomial.tripleCollisionElementary_correct,
    eval_tripleCollisionPolynomial]

theorem pairCollisionValue_rootTuple_ne_zero_iff
    (f : MonicSextic) (hp : Irreducible f.ratPolynomial)
    (x : Fin 2 → ℕ) :
    pairCollisionValue (f, x) ≠ 0 ↔
      Function.Injective
        (pairDescriptorValue x
          (rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree)) := by
  let r := rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree
  have hcast := pairCollisionValue_cast_eq f x r
    (rootTuple_esymm_eq_elementaryValues f hp)
  rw [← collisionProduct_ne_zero_iff]
  rw [← hcast]
  exact (Int.cast_ne_zero :
    ((pairCollisionValue (f, x) : f.ratPolynomial.SplittingField) ≠ 0 ↔
      pairCollisionValue (f, x) ≠ 0)).symm

theorem tripleCollisionValue_rootTuple_ne_zero_iff
    (f : MonicSextic) (hp : Irreducible f.ratPolynomial)
    (x : Fin 2 → ℕ) :
    tripleCollisionValue (f, x) ≠ 0 ↔
      Function.Injective
        (tripleDescriptorValue x
          (rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree)) := by
  let r := rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree
  have hcast := tripleCollisionValue_cast_eq f x r
    (rootTuple_esymm_eq_elementaryValues f hp)
  rw [← collisionProduct_ne_zero_iff]
  rw [← hcast]
  exact (Int.cast_ne_zero :
    ((tripleCollisionValue (f, x) : f.ratPolynomial.SplittingField) ≠ 0 ↔
      tripleCollisionValue (f, x) ≠ 0)).symm

/-! ## Enumeration predicates and termination on irreducible sextics -/

@[reducible] private def parameterEncoding : Encodable (Fin 2 → ℕ) :=
  (inferInstance : Primcodable (Fin 2 → ℕ)).toEncodable

def decodeParameter (n : ℕ) : Option (Fin 2 → ℕ) :=
  @Encodable.decode (Fin 2 → ℕ) parameterEncoding n

def encodeParameter (x : Fin 2 → ℕ) : ℕ :=
  @Encodable.encode (Fin 2 → ℕ) parameterEncoding x

def parameterAt (n : ℕ) : Fin 2 → ℕ :=
  (decodeParameter n).getD (fun _ ↦ 0)

@[simp] theorem parameterAt_encodeParameter (x : Fin 2 → ℕ) :
    parameterAt (encodeParameter x) = x := by
  simp [parameterAt, decodeParameter, encodeParameter]

theorem decodeParameter_primrec : Primrec decodeParameter := by
  exact (Primrec.decode : Primrec
    (@Encodable.decode (Fin 2 → ℕ) parameterEncoding)).of_eq fun _ ↦ rfl

theorem encodeParameter_primrec : Primrec encodeParameter := by
  exact (Primrec.encode : Primrec
    (@Encodable.encode (Fin 2 → ℕ) parameterEncoding)).of_eq fun _ ↦ rfl

theorem parameterAt_primrec : Primrec parameterAt := by
  exact (Primrec.option_getD (α := Fin 2 → ℕ)).comp
    decodeParameter_primrec (Primrec.const fun _ ↦ 0)

noncomputable def pairSeparatesB (f : MonicSextic) (n : ℕ) : Bool :=
  !decide (pairCollisionValue (f, parameterAt n) = 0)

noncomputable def tripleSeparatesB (f : MonicSextic) (n : ℕ) : Bool :=
  !decide (tripleCollisionValue (f, parameterAt n) = 0)

@[simp] theorem pairSeparatesB_eq_true (f : MonicSextic) (n : ℕ) :
    pairSeparatesB f n = true ↔
      pairCollisionValue (f, parameterAt n) ≠ 0 := by
  simp [pairSeparatesB]

@[simp] theorem tripleSeparatesB_eq_true (f : MonicSextic) (n : ℕ) :
    tripleSeparatesB f n = true ↔
      tripleCollisionValue (f, parameterAt n) ≠ 0 := by
  simp [tripleSeparatesB]

theorem pairSeparatesB_computable : Computable₂ pairSeparatesB := by
  have hvalue : Computable fun a : MonicSextic × ℕ ↦
      pairCollisionValue (a.1, parameterAt a.2) :=
    pairCollisionValue_computable.comp
      (Computable.pair Computable.fst
        (parameterAt_primrec.to_comp.comp Computable.snd))
  have heqDec : Computable fun p : ℤ × ℤ ↦ decide (p.1 = p.2) :=
    (Primrec.eq : PrimrecPred fun p : ℤ × ℤ ↦ p.1 = p.2).computablePred.decide
  have heq : ComputablePred fun a : MonicSextic × ℕ ↦
      pairCollisionValue (a.1, parameterAt a.2) = 0 :=
    (heqDec.comp (Computable.pair hvalue (Computable.const 0))).computablePred
  exact heq.not.decide.of_eq fun a ↦ by
    by_cases h : pairCollisionValue (a.1, parameterAt a.2) = 0 <;>
      simp [pairSeparatesB, h]

theorem tripleSeparatesB_computable : Computable₂ tripleSeparatesB := by
  have hvalue : Computable fun a : MonicSextic × ℕ ↦
      tripleCollisionValue (a.1, parameterAt a.2) :=
    tripleCollisionValue_computable.comp
      (Computable.pair Computable.fst
        (parameterAt_primrec.to_comp.comp Computable.snd))
  have heqDec : Computable fun p : ℤ × ℤ ↦ decide (p.1 = p.2) :=
    (Primrec.eq : PrimrecPred fun p : ℤ × ℤ ↦ p.1 = p.2).computablePred.decide
  have heq : ComputablePred fun a : MonicSextic × ℕ ↦
      tripleCollisionValue (a.1, parameterAt a.2) = 0 :=
    (heqDec.comp (Computable.pair hvalue (Computable.const 0))).computablePred
  exact heq.not.decide.of_eq fun a ↦ by
    by_cases h : tripleCollisionValue (a.1, parameterAt a.2) = 0 <;>
      simp [tripleSeparatesB, h]

theorem exists_pairSeparatesB (f : MonicSextic)
    (hp : Irreducible f.ratPolynomial) :
    ∃ n, pairSeparatesB f n = true := by
  let r := rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree
  obtain ⟨x, hx⟩ := exists_pairDescriptorValue_injective r
    (rootTuple_injective f.ratPolynomial hp f.ratPolynomial_natDegree)
  refine ⟨encodeParameter x, ?_⟩
  rw [pairSeparatesB_eq_true, parameterAt_encodeParameter,
    pairCollisionValue_rootTuple_ne_zero_iff f hp]
  exact hx

theorem exists_tripleSeparatesB (f : MonicSextic)
    (hp : Irreducible f.ratPolynomial) :
    ∃ n, tripleSeparatesB f n = true := by
  let r := rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree
  obtain ⟨x, hx⟩ := exists_tripleDescriptorValue_injective r
    (rootTuple_injective f.ratPolynomial hp f.ratPolynomial_natDegree)
  refine ⟨encodeParameter x, ?_⟩
  rw [tripleSeparatesB_eq_true, parameterAt_encodeParameter,
    tripleCollisionValue_rootTuple_ne_zero_iff f hp]
  exact hx

noncomputable def pairSeparatingCode (f : MonicSextic)
    (hp : Irreducible f.ratPolynomial) : ℕ :=
  Nat.find (exists_pairSeparatesB f hp)

noncomputable def tripleSeparatingCode (f : MonicSextic)
    (hp : Irreducible f.ratPolynomial) : ℕ :=
  Nat.find (exists_tripleSeparatesB f hp)

noncomputable def pairSeparatingParameter (f : MonicSextic)
    (hp : Irreducible f.ratPolynomial) : Fin 2 → ℕ :=
  parameterAt (pairSeparatingCode f hp)

noncomputable def tripleSeparatingParameter (f : MonicSextic)
    (hp : Irreducible f.ratPolynomial) : Fin 2 → ℕ :=
  parameterAt (tripleSeparatingCode f hp)

theorem pairSeparatingParameter_injective (f : MonicSextic)
    (hp : Irreducible f.ratPolynomial) :
    Function.Injective
      (pairDescriptorValue (pairSeparatingParameter f hp)
        (rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree)) := by
  rw [← pairCollisionValue_rootTuple_ne_zero_iff f hp]
  exact pairSeparatesB_eq_true f (pairSeparatingCode f hp) |>.mp
    (Nat.find_spec (exists_pairSeparatesB f hp))

theorem tripleSeparatingParameter_injective (f : MonicSextic)
    (hp : Irreducible f.ratPolynomial) :
    Function.Injective
      (tripleDescriptorValue (tripleSeparatingParameter f hp)
        (rootTuple f.ratPolynomial hp f.ratPolynomial_natDegree)) := by
  rw [← tripleCollisionValue_rootTuple_ne_zero_iff f hp]
  exact tripleSeparatesB_eq_true f (tripleSeparatingCode f hp) |>.mp
    (Nat.find_spec (exists_tripleSeparatesB f hp))

end LeanProofs.PolynomialFormulas.SexticSeparatingSearch
