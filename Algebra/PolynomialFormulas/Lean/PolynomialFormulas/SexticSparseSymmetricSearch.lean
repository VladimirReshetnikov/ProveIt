import PolynomialFormulas.SexticEvaluatedResolvents
import PolynomialFormulas.QuinticRadicalPrimrec
import Mathlib.Computability.RE
import Mathlib.Data.List.GetD

/-!
# Recursive sparse symmetric reduction for the sextic resolvents

The fundamental theorem of symmetric polynomials supplies an elementary-
symmetric expression, but its library inverse is intentionally
`noncomputable`.  This file starts an independent, auditable implementation:
finite lists represent sparse polynomials, symbolic equality is checked by
collecting equal exponent vectors, and unbounded minimization can enumerate
candidate elementary-symmetric expressions until that check succeeds.

There is no oracle for polynomial identities here.  Every successful search
candidate carries a finite symbolic equality certificate.
-/

open scoped BigOperators
open MvPolynomial

namespace LeanProofs.PolynomialFormulas.SexticSparseSymmetricSearch

abbrev SparseExponent := Fin 6 → ℕ

structure SparseTerm where
  coeff : ℤ
  powers : SparseExponent
deriving DecidableEq, Repr

def sparseTermEquiv : SparseTerm ≃ ℤ × SparseExponent where
  toFun t := (t.coeff, t.powers)
  invFun t := ⟨t.1, t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable SparseTerm :=
  Primcodable.ofEquiv (ℤ × SparseExponent) sparseTermEquiv

abbrev SparsePolynomial := List SparseTerm

namespace SparseExponent

def zero : SparseExponent := fun _ ↦ 0

def single (i : Fin 6) : SparseExponent := fun j ↦ if j = i then 1 else 0

def add (a b : SparseExponent) : SparseExponent := fun i ↦ a i + b i

end SparseExponent

namespace SparseTerm

noncomputable def toMv (t : SparseTerm) : MvPolynomial (Fin 6) ℤ :=
  monomial (Finsupp.equivFunOnFinite.symm t.powers) t.coeff

def neg (t : SparseTerm) : SparseTerm :=
  ⟨-t.coeff, t.powers⟩

def mul (a b : SparseTerm) : SparseTerm :=
  ⟨a.coeff * b.coeff, SparseExponent.add a.powers b.powers⟩

end SparseTerm

namespace SparsePolynomial

noncomputable def toMv : SparsePolynomial → MvPolynomial (Fin 6) ℤ
  | [] => 0
  | t :: p => t.toMv + toMv p

def const (z : ℤ) : SparsePolynomial :=
  [⟨z, SparseExponent.zero⟩]

def var (i : Fin 6) : SparsePolynomial :=
  [⟨1, SparseExponent.single i⟩]

def add (p q : SparsePolynomial) : SparsePolynomial := p ++ q

def neg (p : SparsePolynomial) : SparsePolynomial := p.map SparseTerm.neg

def sub (p q : SparsePolynomial) : SparsePolynomial := add p (neg q)

def mul (p q : SparsePolynomial) : SparsePolynomial :=
  p.flatMap fun a ↦ q.map fun b ↦ SparseTerm.mul a b

def pow : SparsePolynomial → ℕ → SparsePolynomial
  | _, 0 => const 1
  | p, n + 1 => mul (pow p n) p

/-- The collected coefficient of one exponent vector.  Duplicate terms and
zero coefficients are deliberately allowed in the representation. -/
def coefficient : SparsePolynomial → SparseExponent → ℤ
  | [], _ => 0
  | t :: p, d => (if t.powers = d then t.coeff else 0) + coefficient p d

def supportCandidates (p q : SparsePolynomial) : List SparseExponent :=
  p.map SparseTerm.powers ++ q.map SparseTerm.powers

/-- Executable equality check for sparse polynomials. -/
def equivalentB (p q : SparsePolynomial) : Bool :=
  (supportCandidates p q).all fun d ↦ decide (coefficient p d = coefficient q d)

@[simp] theorem toMv_nil : toMv ([] : SparsePolynomial) = 0 := by
  rfl

@[simp] theorem toMv_cons (t : SparseTerm) (p : SparsePolynomial) :
    toMv (t :: p) = t.toMv + toMv p := by
  rfl

@[simp] theorem toMv_const (z : ℤ) : toMv (const z) = C z := by
  rw [const, toMv_cons, toMv_nil, add_zero, SparseTerm.toMv]
  have hz : Finsupp.equivFunOnFinite.symm SparseExponent.zero =
      (0 : Fin 6 →₀ ℕ) := by
    ext i
    simp [SparseExponent.zero]
  rw [hz]
  rfl

@[simp] theorem toMv_var (i : Fin 6) : toMv (var i) = X i := by
  rw [var, toMv_cons, toMv_nil, add_zero, SparseTerm.toMv]
  have hs : Finsupp.equivFunOnFinite.symm (SparseExponent.single i) =
      Finsupp.single i 1 := by
    ext j
    rw [Finsupp.single_apply]
    change (if j = i then 1 else 0) = if i = j then 1 else 0
    by_cases h : j = i
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [hs]
  rfl

@[simp] theorem toMv_add (p q : SparsePolynomial) :
    toMv (add p q) = toMv p + toMv q := by
  induction p with
  | nil => simp [add]
  | cons t p ih =>
      change toMv (p ++ q) = toMv p + toMv q at ih
      simp [add, ih, add_assoc]

@[simp] theorem toMv_neg (p : SparsePolynomial) :
    toMv (neg p) = -toMv p := by
  induction p with
  | nil => simp [neg]
  | cons t p ih =>
      change toMv (List.map SparseTerm.neg p) = -toMv p at ih
      simp [neg, SparseTerm.neg, SparseTerm.toMv, ih]
      exact add_comm _ _

@[simp] theorem toMv_sub (p q : SparsePolynomial) :
    toMv (sub p q) = toMv p - toMv q := by
  simp [sub, sub_eq_add_neg]

theorem term_toMv_mul (a b : SparseTerm) :
    (SparseTerm.mul a b).toMv = a.toMv * b.toMv := by
  rw [SparseTerm.mul, SparseTerm.toMv, SparseTerm.toMv,
    SparseTerm.toMv, monomial_mul]
  have hpow :
      Finsupp.equivFunOnFinite.symm (SparseExponent.add a.powers b.powers) =
        Finsupp.equivFunOnFinite.symm a.powers +
          Finsupp.equivFunOnFinite.symm b.powers := by
    ext i
    simp [SparseExponent.add]
  rw [hpow]

theorem toMv_map_term_mul (a : SparseTerm) (q : SparsePolynomial) :
    toMv (q.map fun b ↦ SparseTerm.mul a b) = a.toMv * toMv q := by
  induction q with
  | nil => simp
  | cons b q ih => simp [ih, term_toMv_mul, mul_add]

@[simp] theorem toMv_mul (p q : SparsePolynomial) :
    toMv (mul p q) = toMv p * toMv q := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
      change toMv
        (p.flatMap fun a ↦ q.map fun b ↦ SparseTerm.mul a b) =
          toMv p * toMv q at ih
      rw [mul, List.flatMap_cons]
      change toMv (add (q.map fun b ↦ SparseTerm.mul a b)
        (p.flatMap fun a ↦ q.map fun b ↦ SparseTerm.mul a b)) = _
      rw [toMv_add, toMv_map_term_mul, ih, toMv_cons, add_mul]

@[simp] theorem toMv_pow (p : SparsePolynomial) (n : ℕ) :
    toMv (pow p n) = toMv p ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow, ih, pow_succ]

theorem coefficient_toMv (p : SparsePolynomial) (d : SparseExponent) :
    (toMv p).coeff (Finsupp.equivFunOnFinite.symm d) = coefficient p d := by
  induction p with
  | nil => simp [coefficient]
  | cons t p ih =>
      have heq :
          Finsupp.equivFunOnFinite.symm t.powers =
              Finsupp.equivFunOnFinite.symm d ↔ t.powers = d :=
        (Finsupp.equivFunOnFinite.symm.injective.eq_iff)
      simp [SparseTerm.toMv, coefficient, ih, heq]

theorem coefficient_eq_zero_of_not_mem (p : SparsePolynomial)
    (d : SparseExponent) (h : d ∉ p.map SparseTerm.powers) :
    coefficient p d = 0 := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at h
      have hne : t.powers ≠ d := fun htd ↦ h.1 htd.symm
      simp [coefficient, hne, ih h.2]

theorem equivalentB_eq_true_iff (p q : SparsePolynomial) :
    equivalentB p q = true ↔ toMv p = toMv q := by
  rw [equivalentB, List.all_eq_true]
  constructor
  · intro h
    ext m
    let d : SparseExponent := Finsupp.equivFunOnFinite m
    have hm : Finsupp.equivFunOnFinite.symm d = m := by
      simp [d]
    rw [← hm, coefficient_toMv, coefficient_toMv]
    by_cases hp : d ∈ p.map SparseTerm.powers
    · exact of_decide_eq_true (h d (by simp [supportCandidates, hp]))
    · by_cases hq : d ∈ q.map SparseTerm.powers
      · exact of_decide_eq_true (h d (by simp [supportCandidates, hq]))
      · rw [coefficient_eq_zero_of_not_mem p d hp,
          coefficient_eq_zero_of_not_mem q d hq]
  · intro h d hd
    apply decide_eq_true
    have hc := congrArg
      (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm d)) h
    simpa only [coefficient_toMv] using hc

/-- Every mathematical multivariate polynomial has a finite sparse-list
representative.  This theorem is used only to prove that enumeration
terminates; the enumerator itself manipulates the lists above. -/
theorem toMv_surjective : Function.Surjective toMv := by
  intro P
  induction P using MvPolynomial.induction_on' with
  | monomial d z =>
      refine ⟨[⟨z, Finsupp.equivFunOnFinite d⟩], ?_⟩
      rw [toMv_cons, toMv_nil, add_zero, SparseTerm.toMv]
      simp
  | add p q hp hq =>
      obtain ⟨ps, hps⟩ := hp
      obtain ⟨qs, hqs⟩ := hq
      exact ⟨add ps qs, by simp [hps, hqs]⟩

/-! ## Sparse substitution -/

/-- Product of six sparse polynomials.  Writing the six factors explicitly
keeps the executable representation independent of any classical `Finset`
enumeration. -/
def product6 (f : Fin 6 → SparsePolynomial) : SparsePolynomial :=
  mul (f 0) (mul (f 1) (mul (f 2) (mul (f 3) (mul (f 4) (f 5)))))

@[simp] theorem toMv_product6 (f : Fin 6 → SparsePolynomial) :
    toMv (product6 f) = ∏ i, toMv (f i) := by
  simp [product6, Fin.prod_univ_succ]

def substituteTerm (values : Fin 6 → SparsePolynomial)
    (t : SparseTerm) : SparsePolynomial :=
  mul (const t.coeff) (product6 fun i ↦ pow (values i) (t.powers i))

def substitute (values : Fin 6 → SparsePolynomial) :
    SparsePolynomial → SparsePolynomial
  | [] => []
  | t :: p => add (substituteTerm values t) (substitute values p)

theorem toMv_substituteTerm (values : Fin 6 → SparsePolynomial)
    (t : SparseTerm) :
    toMv (substituteTerm values t) =
      MvPolynomial.eval₂ C (fun i ↦ toMv (values i)) t.toMv := by
  simp [substituteTerm, SparseTerm.toMv, MvPolynomial.eval₂_monomial]

theorem toMv_substitute (values : Fin 6 → SparsePolynomial)
    (p : SparsePolynomial) :
    toMv (substitute values p) =
      MvPolynomial.eval₂ C (fun i ↦ toMv (values i)) (toMv p) := by
  induction p with
  | nil => simp [substitute]
  | cons t p ih =>
      simp [substitute, toMv_substituteTerm, ih,
        MvPolynomial.eval₂_add]

def sixIndices : List (Fin 6) := List.ofFn fun i ↦ i

/-- Executable elementary-symmetric recurrence on a list of variables. -/
def esymmList : List (Fin 6) → ℕ → SparsePolynomial
  | _, 0 => const 1
  | [], _ + 1 => []
  | i :: is, k + 1 =>
      add (esymmList is (k + 1)) (mul (var i) (esymmList is k))

/-- Fully executable sparse form of elementary symmetric polynomial number
`i+1`. -/
def esymmSparse (i : Fin 6) : SparsePolynomial :=
  esymmList sixIndices (i + 1)

theorem multiset_esymm_cons_succ
    (a : MvPolynomial (Fin 6) ℤ)
    (s : Multiset (MvPolynomial (Fin 6) ℤ)) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  have hmul (u : Multiset (MvPolynomial (Fin 6) ℤ)) :
      (u.map fun x ↦ a * x).sum = a * u.sum := by
    induction u using Multiset.induction_on with
    | empty => simp
    | @cons x u ih => simp [ih, mul_add]
  simp [Multiset.esymm, Multiset.powersetCard_cons,
    Multiset.map_map]
  simpa only [Multiset.map_map, Function.comp_apply] using
    hmul ((Multiset.powersetCard k s).map Multiset.prod)

theorem toMv_esymmList (is : List (Fin 6)) (k : ℕ) :
    toMv (esymmList is k) =
      ((is : Multiset (Fin 6)).map fun i ↦
        (X i : MvPolynomial (Fin 6) ℤ)).esymm k := by
  induction is generalizing k with
  | nil =>
      cases k <;> simp [esymmList, Multiset.esymm]
  | cons i is ih =>
      cases k with
      | zero => simp [esymmList, Multiset.esymm]
      | succ k =>
          rw [esymmList, toMv_add, toMv_mul, toMv_var, ih, ih]
          exact multiset_esymm_cons_succ (X i) _ k |>.symm

theorem sixIndices_toMultiset :
    (sixIndices : Multiset (Fin 6)) = (Finset.univ : Finset (Fin 6)).val := by
  decide

theorem toMv_esymmSparse (i : Fin 6) :
    toMv (esymmSparse i) = MvPolynomial.esymm (Fin 6) ℤ (i + 1) := by
  rw [esymmSparse, toMv_esymmList, MvPolynomial.esymm_eq_multiset_esymm,
    sixIndices_toMultiset]

/-- Substitute the six elementary symmetric polynomials into a candidate
formula. -/
def substituteEsymm (q : SparsePolynomial) : SparsePolynomial :=
  substitute esymmSparse q

theorem toMv_substituteEsymm (q : SparsePolynomial) :
    toMv (substituteEsymm q) =
      MvPolynomial.aeval
        (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
        (toMv q) := by
  rw [substituteEsymm, toMv_substitute]
  simp only [toMv_esymmSparse, MvPolynomial.aeval_def]
  rw [← MvPolynomial.C_eq_algebraMap]

/-! ## Certified enumeration -/

/-- A sparse symmetric polynomial has a sparse elementary-symmetric
representative.  This is the termination proof for the enumerator below. -/
theorem exists_sparse_elementary_representation (p : SparsePolynomial)
    (hp : (toMv p).IsSymmetric) :
    ∃ q : SparsePolynomial, equivalentB (substituteEsymm q) p = true := by
  let sp : MvPolynomial.symmetricSubalgebra (Fin 6) ℤ := ⟨toMv p, hp⟩
  let Q : MvPolynomial (Fin 6) ℤ :=
    (MvPolynomial.esymmAlgEquiv (Fin 6) ℤ
      (show Fintype.card (Fin 6) = 6 by simp)).symm sp
  obtain ⟨q, hq⟩ := toMv_surjective Q
  refine ⟨q, (equivalentB_eq_true_iff _ _).2 ?_⟩
  rw [toMv_substituteEsymm, hq]
  have h := congrArg Subtype.val
    ((MvPolynomial.esymmAlgEquiv (Fin 6) ℤ
      (show Fintype.card (Fin 6) = 6 by simp)).apply_symm_apply sp)
  simpa only [MvPolynomial.esymmAlgEquiv_apply,
    MvPolynomial.esymmAlgHom_apply, sp] using h

@[reducible] private def sparseEncoding : Encodable SparsePolynomial :=
  (inferInstance : Primcodable SparsePolynomial).toEncodable

def decodeSparse (n : ℕ) : Option SparsePolynomial :=
  @Encodable.decode SparsePolynomial sparseEncoding n

def encodeSparse (p : SparsePolynomial) : ℕ :=
  @Encodable.encode SparsePolynomial sparseEncoding p

@[simp] theorem decodeSparse_encodeSparse (p : SparsePolynomial) :
    decodeSparse (encodeSparse p) = some p := by
  simp [decodeSparse, encodeSparse]

/-- The finite certificate checked at enumeration index `n`. -/
def representsB (p : SparsePolynomial) (n : ℕ) : Bool :=
  match decodeSparse n with
  | none => false
  | some q => equivalentB (substituteEsymm q) p

theorem representsB_sound {p : SparsePolynomial} {n : ℕ}
    (h : representsB p n = true) :
    ∃ q, decodeSparse n = some q ∧
      MvPolynomial.aeval
          (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
          (toMv q) = toMv p := by
  unfold representsB at h
  cases hq : decodeSparse n with
  | none => simp [hq] at h
  | some q =>
      refine ⟨q, rfl, ?_⟩
      rw [← toMv_substituteEsymm]
      exact (equivalentB_eq_true_iff _ _).1 (by simpa [hq] using h)

theorem exists_representsB (p : SparsePolynomial)
    (hp : (toMv p).IsSymmetric) : ∃ n, representsB p n = true := by
  obtain ⟨q, hq⟩ := exists_sparse_elementary_representation p hp
  exact ⟨encodeSparse q, by simp [representsB, hq]⟩

/-! ## Recursiveness of the certificate checker -/

open LeanProofs.PolynomialFormulas.QuinticRadicalPrimrec

theorem sparseTermEquiv_primrec : Primrec sparseTermEquiv :=
  Primrec.of_equiv

theorem sparseTermEquiv_symm_primrec : Primrec sparseTermEquiv.symm :=
  Primrec.of_equiv_symm

theorem sparseTerm_coeff_primrec : Primrec SparseTerm.coeff :=
  Primrec.fst.comp sparseTermEquiv_primrec

theorem sparseTerm_powers_primrec : Primrec SparseTerm.powers :=
  Primrec.snd.comp sparseTermEquiv_primrec

theorem sparseExponent_add_primrec : Primrec₂ SparseExponent.add := by
  have h : Primrec fun p : SparseExponent × SparseExponent ↦
      SparseExponent.add p.1 p.2 := by
    apply Primrec.fin_curry.mpr
    have hpoint : Primrec₂ fun (i : Fin 6) ↦
        fun p : SparseExponent × SparseExponent ↦ p.1 i + p.2 i :=
      Primrec.fin_curry₁.mpr fun i ↦
        Primrec.nat_add.comp
          (Primrec.fin_app.comp Primrec.fst (Primrec.const i))
          (Primrec.fin_app.comp Primrec.snd (Primrec.const i))
    exact hpoint.swap
  exact h

theorem sparseTerm_neg_primrec : Primrec SparseTerm.neg := by
  apply (Primrec.of_equiv_iff sparseTermEquiv).mp
  exact Primrec.pair
    (int_neg_primrec.comp sparseTerm_coeff_primrec)
    sparseTerm_powers_primrec

theorem sparseTerm_mul_primrec : Primrec₂ SparseTerm.mul := by
  change Primrec fun p : SparseTerm × SparseTerm ↦ SparseTerm.mul p.1 p.2
  apply (Primrec.of_equiv_iff sparseTermEquiv).mp
  exact Primrec.pair
    (int_mul_primrec.comp
      (sparseTerm_coeff_primrec.comp Primrec.fst)
      (sparseTerm_coeff_primrec.comp Primrec.snd))
    (sparseExponent_add_primrec.comp
      (sparseTerm_powers_primrec.comp Primrec.fst)
      (sparseTerm_powers_primrec.comp Primrec.snd))

theorem add_primrec : Primrec₂ SparsePolynomial.add :=
  Primrec.list_append

theorem neg_primrec : Primrec SparsePolynomial.neg := by
  exact (Primrec.list_map Primrec.id
    (sparseTerm_neg_primrec.comp Primrec.snd).to₂).of_eq fun _ ↦ rfl

theorem mul_primrec : Primrec₂ SparsePolynomial.mul := by
  change Primrec fun p : SparsePolynomial × SparsePolynomial ↦
    SparsePolynomial.mul p.1 p.2
  apply Primrec.list_flatMap Primrec.fst
  change Primrec₂ fun (p : SparsePolynomial × SparsePolynomial)
    (a : SparseTerm) ↦ p.2.map fun b ↦ SparseTerm.mul a b
  apply Primrec.list_map (Primrec.snd.comp Primrec.fst)
  have hg : Primrec₂ fun
      (q : (SparsePolynomial × SparsePolynomial) × SparseTerm)
      (b : SparseTerm) ↦ SparseTerm.mul q.2 b := by
    change Primrec fun
      z : ((SparsePolynomial × SparsePolynomial) × SparseTerm) × SparseTerm ↦
        SparseTerm.mul z.1.2 z.2
    exact sparseTerm_mul_primrec.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact hg

theorem const_primrec : Primrec SparsePolynomial.const := by
  have hterm : Primrec fun z : ℤ ↦
      (⟨z, SparseExponent.zero⟩ : SparseTerm) := by
    apply (Primrec.of_equiv_iff sparseTermEquiv).mp
    exact Primrec.pair Primrec.id (Primrec.const SparseExponent.zero)
  exact Primrec.list_cons.comp hterm (Primrec.const [])

theorem pow_primrec : Primrec₂ SparsePolynomial.pow := by
  have hstep : Primrec₂ fun p : SparsePolynomial ↦
      fun q : ℕ × SparsePolynomial ↦ SparsePolynomial.mul q.2 p :=
    by
      change Primrec fun z : SparsePolynomial × (ℕ × SparsePolynomial) ↦
        SparsePolynomial.mul z.2.2 z.1
      exact mul_primrec.comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  have hbase : Primrec fun _p : SparsePolynomial ↦
      SparsePolynomial.const 1 := Primrec.const _
  exact (Primrec.nat_rec hbase hstep).of_eq fun p n ↦ by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Nat.rec_add_one, pow, ih]

theorem esymmFactor_primrec (i : Fin 6) : Primrec fun t : SparseTerm ↦
    SparsePolynomial.pow (esymmSparse i) (t.powers i) := by
  exact pow_primrec.comp (Primrec.const (esymmSparse i))
    (Primrec.fin_app.comp sparseTerm_powers_primrec (Primrec.const i))

theorem esymmProduct_primrec : Primrec fun t : SparseTerm ↦
    product6 fun i ↦ SparsePolynomial.pow (esymmSparse i) (t.powers i) := by
  exact mul_primrec.comp (esymmFactor_primrec 0) <|
    mul_primrec.comp (esymmFactor_primrec 1) <|
      mul_primrec.comp (esymmFactor_primrec 2) <|
        mul_primrec.comp (esymmFactor_primrec 3) <|
          mul_primrec.comp (esymmFactor_primrec 4) (esymmFactor_primrec 5)

theorem substituteTerm_esymm_primrec : Primrec fun t : SparseTerm ↦
    substituteTerm esymmSparse t := by
  exact mul_primrec.comp
    (const_primrec.comp sparseTerm_coeff_primrec) esymmProduct_primrec

theorem substituteEsymm_primrec : Primrec substituteEsymm := by
  have hstep : Primrec₂ fun _p : SparsePolynomial ↦
      fun u : SparseTerm × SparsePolynomial × SparsePolynomial ↦
        SparsePolynomial.add (substituteTerm esymmSparse u.1) u.2.2 := by
    change Primrec fun z : SparsePolynomial ×
        (SparseTerm × SparsePolynomial × SparsePolynomial) ↦
      SparsePolynomial.add (substituteTerm esymmSparse z.2.1) z.2.2.2
    exact add_primrec.comp
      (substituteTerm_esymm_primrec.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_rec Primrec.id (Primrec.const []) hstep).of_eq fun p ↦ by
    induction p with
    | nil => rfl
    | cons t p ih =>
        change List.recOn p []
          (fun b l IH ↦ SparsePolynomial.add
            (substituteTerm esymmSparse b) IH) =
          substitute esymmSparse p at ih
        change SparsePolynomial.add (substituteTerm esymmSparse t)
          (List.recOn p [] (fun b l IH ↦ SparsePolynomial.add
            (substituteTerm esymmSparse b) IH)) =
          SparsePolynomial.add (substituteTerm esymmSparse t)
            (substitute esymmSparse p)
        rw [ih]

theorem coefficient_primrec : Primrec₂ SparsePolynomial.coefficient := by
  have hstep : Primrec₂ fun a : SparsePolynomial × SparseExponent ↦
      fun u : SparseTerm × ℤ ↦
        (if u.1.powers = a.2 then u.1.coeff else 0) + u.2 := by
    change Primrec fun z : (SparsePolynomial × SparseExponent) ×
        (SparseTerm × ℤ) ↦
      (if z.2.1.powers = z.1.2 then z.2.1.coeff else 0) + z.2.2
    have heq : PrimrecPred fun z : (SparsePolynomial × SparseExponent) ×
        (SparseTerm × ℤ) ↦ z.2.1.powers = z.1.2 :=
      Primrec.eq.comp
        (sparseTerm_powers_primrec.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst)
    have hif : Primrec fun z : (SparsePolynomial × SparseExponent) ×
        (SparseTerm × ℤ) ↦
      if z.2.1.powers = z.1.2 then z.2.1.coeff else 0 :=
      Primrec.ite heq
        (sparseTerm_coeff_primrec.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const 0)
    exact int_add_primrec.comp hif (Primrec.snd.comp Primrec.snd)
  have hfold : Primrec fun a : SparsePolynomial × SparseExponent ↦
      a.1.foldr
        (fun t z ↦ (if t.powers = a.2 then t.coeff else 0) + z) 0 :=
    Primrec.list_foldr Primrec.fst (Primrec.const 0) hstep
  exact hfold.of_eq fun a ↦ by
    induction a.1 with
    | nil => rfl
    | cons t p ih => simp only [List.foldr_cons, coefficient, ih]

theorem powersList_primrec : Primrec fun p : SparsePolynomial ↦
    p.map SparseTerm.powers := by
  exact (Primrec.list_map Primrec.id
    (sparseTerm_powers_primrec.comp Primrec.snd).to₂).of_eq fun _ ↦ rfl

theorem supportCandidates_primrec : Primrec₂ supportCandidates := by
  exact Primrec.list_append.comp
    (powersList_primrec.comp Primrec.fst)
    (powersList_primrec.comp Primrec.snd)

theorem equivalentB_primrec : Primrec₂ equivalentB := by
  have hR : PrimrecRel fun d : SparseExponent ↦
      fun p : SparsePolynomial × SparsePolynomial ↦
        coefficient p.1 d = coefficient p.2 d := by
    change PrimrecPred fun z : SparseExponent ×
        (SparsePolynomial × SparsePolynomial) ↦
      coefficient z.2.1 z.1 = coefficient z.2.2 z.1
    exact Primrec.eq.comp
      (coefficient_primrec.comp
        (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (coefficient_primrec.comp
        (Primrec.snd.comp Primrec.snd) Primrec.fst)
  have hall : PrimrecPred fun p : SparsePolynomial × SparsePolynomial ↦
      ∀ d ∈ supportCandidates p.1 p.2,
        coefficient p.1 d = coefficient p.2 d :=
    hR.forall_mem_list.comp
      (supportCandidates_primrec.comp Primrec.fst Primrec.snd) Primrec.id
  change Primrec fun p : SparsePolynomial × SparsePolynomial ↦
    equivalentB p.1 p.2
  exact hall.decide.of_eq fun p ↦ by
    apply Bool.eq_iff_iff.mpr
    simp only [equivalentB, List.all_eq_true, decide_eq_true_eq]

theorem decodeSparse_primrec : Primrec decodeSparse := by
  exact (Primrec.decode : Primrec
    (@Encodable.decode SparsePolynomial sparseEncoding)).of_eq fun _ ↦ rfl

theorem encodeSparse_primrec : Primrec encodeSparse := by
  exact (Primrec.encode : Primrec
    (@Encodable.encode SparsePolynomial sparseEncoding)).of_eq fun _ ↦ rfl

theorem representsB_primrec : Primrec₂ representsB := by
  change Primrec fun a : SparsePolynomial × ℕ ↦ representsB a.1 a.2
  have hnone : Primrec fun _a : SparsePolynomial × ℕ ↦ false :=
    Primrec.const false
  have hsome : Primrec₂ fun a : SparsePolynomial × ℕ ↦
      fun q : SparsePolynomial ↦ equivalentB (substituteEsymm q) a.1 := by
    change Primrec fun z : (SparsePolynomial × ℕ) × SparsePolynomial ↦
      equivalentB (substituteEsymm z.2) z.1.1
    exact equivalentB_primrec.comp
      (substituteEsymm_primrec.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  exact (Primrec.option_casesOn
    (decodeSparse_primrec.comp Primrec.snd) hnone hsome).of_eq fun a ↦ by
      simp only [representsB]
      cases decodeSparse a.2 <;> rfl

section TotalSearch

variable {α : Type*} [Primcodable α]

/-- Least certificate code for a recursively generated family of symmetric
sparse polynomials. -/
noncomputable def elementaryCode
    (target : α → SparsePolynomial)
    (hsymm : ∀ a, (toMv (target a)).IsSymmetric) (a : α) : ℕ :=
  Nat.find (exists_representsB (target a) (hsymm a))

theorem elementaryCode_spec
    (target : α → SparsePolynomial)
    (hsymm : ∀ a, (toMv (target a)).IsSymmetric) (a : α) :
    representsB (target a) (elementaryCode target hsymm a) = true :=
  Nat.find_spec (exists_representsB (target a) (hsymm a))

/-- Unbounded enumeration is an ordinary total recursive function because a
certificate exists for every input and the certificate test is primitive
recursive. -/
theorem elementaryCode_computable
    (target : α → SparsePolynomial) (htarget : Computable target)
    (hsymm : ∀ a, (toMv (target a)).IsSymmetric) :
    Computable (elementaryCode target hsymm) := by
  have htest : Computable₂ fun a : α ↦ fun n : ℕ ↦
      representsB (target a) n := by
    have ht₂ : Computable₂ fun a : α ↦ fun _n : ℕ ↦ target a :=
      (htarget.comp (Computable.fst : Computable
        (@Prod.fst α ℕ))).to₂
    have hn₂ : Computable₂ fun _a : α ↦ fun n : ℕ ↦ n :=
      (Computable.snd : Computable (@Prod.snd α ℕ)).to₂
    exact representsB_primrec.to_comp.comp₂ ht₂ hn₂
  have htest' : Computable fun p : α × ℕ ↦
      representsB (target p.1) p.2 := htest
  have hpred : ComputablePred fun p : α × ℕ ↦
      representsB (target p.1) p.2 = true :=
    (htest'.of_eq fun p ↦ by
      cases h : representsB (target p.1) p.2 <;> simp [h]).computablePred
  exact Computable.find hpred
    (fun a ↦ exists_representsB (target a) (hsymm a))

/-- Decode the least verified formula.  The default branch is unreachable by
`elementaryCode_spec`, but makes the definition total without choice. -/
noncomputable def elementarySparse
    (target : α → SparsePolynomial)
    (hsymm : ∀ a, (toMv (target a)).IsSymmetric) (a : α) :
    SparsePolynomial :=
  (decodeSparse (elementaryCode target hsymm a)).getD []

theorem elementarySparse_correct
    (target : α → SparsePolynomial)
    (hsymm : ∀ a, (toMv (target a)).IsSymmetric) (a : α) :
    MvPolynomial.aeval
        (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
        (toMv (elementarySparse target hsymm a)) =
      toMv (target a) := by
  obtain ⟨q, hdecode, hq⟩ :=
    representsB_sound (elementaryCode_spec target hsymm a)
  rw [elementarySparse, hdecode]
  exact hq

theorem elementarySparse_computable
    (target : α → SparsePolynomial) (htarget : Computable target)
    (hsymm : ∀ a, (toMv (target a)).IsSymmetric) :
    Computable (elementarySparse target hsymm) := by
  have hcode := elementaryCode_computable target htarget hsymm
  exact (Primrec.option_getD (α := SparsePolynomial)).to_comp.comp
    (decodeSparse_primrec.to_comp.comp hcode) (Computable.const [])

end TotalSearch

/-! ## Recursive coefficient lists for products of linear factors -/

abbrev SparseCoefficientList := List SparsePolynomial

namespace SparseCoefficientList

def add : SparseCoefficientList → SparseCoefficientList → SparseCoefficientList
  | p, q =>
      (List.range (max p.length q.length)).map fun n ↦
        SparsePolynomial.add (p.getD n []) (q.getD n [])

def scale (a : SparsePolynomial) (p : SparseCoefficientList) :
    SparseCoefficientList := p.map (SparsePolynomial.mul a)

def shift (p : SparseCoefficientList) : SparseCoefficientList := [] :: p

/-- Ascending coefficients of `∏ᵢ (T - roots[i])`. -/
def linearProduct : List SparsePolynomial → SparseCoefficientList
  | [] => [SparsePolynomial.const 1]
  | a :: roots =>
      let q := linearProduct roots
      add (scale (SparsePolynomial.neg a) q) (shift q)

noncomputable def toPolynomial : SparseCoefficientList →
    Polynomial (MvPolynomial (Fin 6) ℤ)
  | [] => 0
  | a :: p => Polynomial.C (SparsePolynomial.toMv a) +
      Polynomial.X * toPolynomial p

@[simp] theorem toPolynomial_nil : toPolynomial [] = 0 := rfl

@[simp] theorem toPolynomial_cons (a : SparsePolynomial)
    (p : SparseCoefficientList) :
    toPolynomial (a :: p) = Polynomial.C (SparsePolynomial.toMv a) +
      Polynomial.X * toPolynomial p := rfl

@[simp] theorem coeff_toPolynomial (p : SparseCoefficientList) (n : ℕ) :
    (toPolynomial p).coeff n = SparsePolynomial.toMv (p.getD n []) := by
  induction p generalizing n with
  | nil => simp
  | cons a p ih =>
      cases n with
      | zero => simp
      | succ n => simp [ih, Polynomial.coeff_X_mul]

@[simp] theorem toPolynomial_add (p q : SparseCoefficientList) :
    toPolynomial (add p q) = toPolynomial p + toPolynomial q := by
  ext n
  simp only [coeff_toPolynomial, Polynomial.coeff_add]
  by_cases h : n < max p.length q.length
  · rw [List.getD_eq_getElem (add p q) []]
    · simp [add, h]
    · simpa [add] using h
  · have hp : p.length ≤ n := le_trans (Nat.le_max_left _ _) (Nat.le_of_not_gt h)
    have hq : q.length ≤ n := le_trans (Nat.le_max_right _ _) (Nat.le_of_not_gt h)
    rw [List.getD_eq_default (add p q) []]
    · rw [List.getD_eq_default p [] hp, List.getD_eq_default q [] hq]
      simp
    · simpa [add] using Nat.le_of_not_gt h

@[simp] theorem toPolynomial_scale (a : SparsePolynomial)
    (p : SparseCoefficientList) :
    toPolynomial (scale a p) =
      Polynomial.C (SparsePolynomial.toMv a) * toPolynomial p := by
  induction p with
  | nil => simp [scale]
  | cons b p ih =>
      change toPolynomial (List.map (SparsePolynomial.mul a) p) =
        Polynomial.C (SparsePolynomial.toMv a) * toPolynomial p at ih
      simp [scale, ih, mul_add]
      ring

@[simp] theorem toPolynomial_shift (p : SparseCoefficientList) :
    toPolynomial (shift p) = Polynomial.X * toPolynomial p := by
  simp [shift]

theorem toPolynomial_linearProduct (roots : List SparsePolynomial) :
    toPolynomial (linearProduct roots) =
      (roots.map fun a ↦
        (Polynomial.X - Polynomial.C (SparsePolynomial.toMv a))).prod := by
  induction roots with
  | nil => simp [linearProduct]
  | cons a roots ih =>
      simp only [linearProduct, toPolynomial_add, toPolynomial_scale,
        SparsePolynomial.toMv_neg, toPolynomial_shift, ih, List.map_cons,
        List.prod_cons, map_neg, Polynomial.C_neg]
      ring

end SparseCoefficientList

/-! ## The actual sparse pair/triple descriptor resolvents -/

open LeanProofs.PolynomialFormulas.Fin6BlockSystems
open LeanProofs.PolynomialFormulas.SexticPartitionResolvents
open LeanProofs.PolynomialFormulas.SexticSeparatingInvariants
open LeanProofs.PolynomialFormulas.SexticEvaluatedResolvents

def natConst (n : ℕ) : SparsePolynomial := SparsePolynomial.const (Int.ofNat n)

def product2 (f : Fin 2 → SparsePolynomial) : SparsePolynomial :=
  SparsePolynomial.mul (f 0) (f 1)

def product3 (f : Fin 3 → SparsePolynomial) : SparsePolynomial :=
  SparsePolynomial.mul (f 0) (SparsePolynomial.mul (f 1) (f 2))

def pairSparseBlockValue (x : Fin 2 → ℕ) (p : PairPartition)
    (b : Fin 3) : SparsePolynomial :=
  product2 fun s ↦ SparsePolynomial.sub (natConst (x 1))
    (SparsePolynomial.var (pairMember p b s))

def tripleSparseBlockValue (x : Fin 2 → ℕ) (p : TriplePartition)
    (b : Fin 2) : SparsePolynomial :=
  product3 fun s ↦ SparsePolynomial.sub (natConst (x 1))
    (SparsePolynomial.var (tripleMember p b s))

def pairSparseDescriptorValue (x : Fin 2 → ℕ)
    (p : PairPartition) : SparsePolynomial :=
  product3 fun b ↦ SparsePolynomial.sub (natConst (x 0))
    (pairSparseBlockValue x p b)

def tripleSparseDescriptorValue (x : Fin 2 → ℕ)
    (p : TriplePartition) : SparsePolynomial :=
  product2 fun b ↦ SparsePolynomial.sub (natConst (x 0))
    (tripleSparseBlockValue x p b)

def pairSparseResolvent (x : Fin 2 → ℕ) : SparseCoefficientList :=
  SparseCoefficientList.linearProduct
    (List.ofFn fun p : PairPartition ↦ pairSparseDescriptorValue x p)

def tripleSparseResolvent (x : Fin 2 → ℕ) : SparseCoefficientList :=
  SparseCoefficientList.linearProduct
    (List.ofFn fun p : TriplePartition ↦ tripleSparseDescriptorValue x p)

def pairSparseResolventCoefficient (a : (Fin 2 → ℕ) × Fin 16) :
    SparsePolynomial := (pairSparseResolvent a.1).getD a.2 []

def tripleSparseResolventCoefficient (a : (Fin 2 → ℕ) × Fin 11) :
    SparsePolynomial := (tripleSparseResolvent a.1).getD a.2 []

@[simp] theorem toMv_natConst (n : ℕ) :
    SparsePolynomial.toMv (natConst n) = (n : MvPolynomial (Fin 6) ℤ) := by
  simp [natConst]

@[simp] theorem toMv_product2 (f : Fin 2 → SparsePolynomial) :
    SparsePolynomial.toMv (product2 f) = ∏ i, SparsePolynomial.toMv (f i) := by
  simp [product2, Fin.prod_univ_succ]

@[simp] theorem toMv_product3 (f : Fin 3 → SparsePolynomial) :
    SparsePolynomial.toMv (product3 f) = ∏ i, SparsePolynomial.toMv (f i) := by
  simp [product3, Fin.prod_univ_succ]

@[simp] theorem toMv_pairSparseBlockValue (x : Fin 2 → ℕ)
    (p : PairPartition) (b : Fin 3) :
    SparsePolynomial.toMv (pairSparseBlockValue x p b) =
      ∏ s : Fin 2,
        ((x 1 : MvPolynomial (Fin 6) ℤ) - X (pairMember p b s)) := by
  simp [pairSparseBlockValue]

@[simp] theorem toMv_tripleSparseBlockValue (x : Fin 2 → ℕ)
    (p : TriplePartition) (b : Fin 2) :
    SparsePolynomial.toMv (tripleSparseBlockValue x p b) =
      ∏ s : Fin 3,
        ((x 1 : MvPolynomial (Fin 6) ℤ) - X (tripleMember p b s)) := by
  simp [tripleSparseBlockValue]

@[simp] theorem toMv_pairSparseDescriptorValue (x : Fin 2 → ℕ)
    (p : PairPartition) :
    SparsePolynomial.toMv (pairSparseDescriptorValue x p) =
      ∏ b : Fin 3,
        ((x 0 : MvPolynomial (Fin 6) ℤ) -
          ∏ s : Fin 2,
            ((x 1 : MvPolynomial (Fin 6) ℤ) - X (pairMember p b s))) := by
  simp [pairSparseDescriptorValue]

@[simp] theorem toMv_tripleSparseDescriptorValue (x : Fin 2 → ℕ)
    (p : TriplePartition) :
    SparsePolynomial.toMv (tripleSparseDescriptorValue x p) =
      ∏ b : Fin 2,
        ((x 0 : MvPolynomial (Fin 6) ℤ) -
          ∏ s : Fin 3,
            ((x 1 : MvPolynomial (Fin 6) ℤ) - X (tripleMember p b s))) := by
  simp [tripleSparseDescriptorValue]

theorem pairDescriptorValue_rootVariables_eq_sparse
    (x : Fin 2 → ℕ) (p : PairPartition) :
    pairDescriptorValue x (fun i ↦ (X i : MvPolynomial (Fin 6) ℤ)) p =
      SparsePolynomial.toMv (pairSparseDescriptorValue x p) := by
  classical
  rw [toMv_pairSparseDescriptorValue]
  simp [pairDescriptorValue, pairBivariateDescriptor, bivariateDescriptor,
    pairBlocks, pairBlock, bivariateRootPolynomial,
    Finset.prod_image (pairBlock_injective p).injOn,
    Finset.prod_insert, pairMember_ne, Fin.prod_univ_succ]

theorem tripleDescriptorValue_rootVariables_eq_sparse
    (x : Fin 2 → ℕ) (p : TriplePartition) :
    tripleDescriptorValue x (fun i ↦ (X i : MvPolynomial (Fin 6) ℤ)) p =
      SparsePolynomial.toMv (tripleSparseDescriptorValue x p) := by
  classical
  rw [toMv_tripleSparseDescriptorValue]
  simp [tripleDescriptorValue, tripleBivariateDescriptor, bivariateDescriptor,
    tripleBlocks, tripleBlock, bivariateRootPolynomial,
    Finset.prod_image (tripleBlock_injective p).injOn,
    Finset.prod_insert, tripleMember_pairwise_ne, Fin.prod_univ_succ]

theorem pairSparseResolvent_toPolynomial (x : Fin 2 → ℕ) :
    SparseCoefficientList.toPolynomial (pairSparseResolvent x) =
      pairUniversalEvaluatedResolvent x := by
  rw [pairSparseResolvent,
    SparseCoefficientList.toPolynomial_linearProduct]
  simp only [List.map_ofFn, List.prod_ofFn,
    pairUniversalEvaluatedResolvent, pairEvaluatedResolvent]
  apply Finset.prod_congr rfl
  intro p hp
  change Polynomial.X - Polynomial.C
      (SparsePolynomial.toMv (pairSparseDescriptorValue x p)) =
    Polynomial.X - Polynomial.C
      (pairDescriptorValue x
        (fun i ↦ (X i : MvPolynomial (Fin 6) ℤ)) p)
  rw [pairDescriptorValue_rootVariables_eq_sparse]

theorem tripleSparseResolvent_toPolynomial (x : Fin 2 → ℕ) :
    SparseCoefficientList.toPolynomial (tripleSparseResolvent x) =
      tripleUniversalEvaluatedResolvent x := by
  rw [tripleSparseResolvent,
    SparseCoefficientList.toPolynomial_linearProduct]
  simp only [List.map_ofFn, List.prod_ofFn,
    tripleUniversalEvaluatedResolvent, tripleEvaluatedResolvent]
  apply Finset.prod_congr rfl
  intro p hp
  change Polynomial.X - Polynomial.C
      (SparsePolynomial.toMv (tripleSparseDescriptorValue x p)) =
    Polynomial.X - Polynomial.C
      (tripleDescriptorValue x
        (fun i ↦ (X i : MvPolynomial (Fin 6) ℤ)) p)
  rw [tripleDescriptorValue_rootVariables_eq_sparse]

theorem pairSparseResolventCoefficient_toMv
    (a : (Fin 2 → ℕ) × Fin 16) :
    SparsePolynomial.toMv (pairSparseResolventCoefficient a) =
      (pairUniversalEvaluatedResolvent a.1).coeff a.2 := by
  rw [← pairSparseResolvent_toPolynomial a.1,
    SparseCoefficientList.coeff_toPolynomial]
  rfl

theorem tripleSparseResolventCoefficient_toMv
    (a : (Fin 2 → ℕ) × Fin 11) :
    SparsePolynomial.toMv (tripleSparseResolventCoefficient a) =
      (tripleUniversalEvaluatedResolvent a.1).coeff a.2 := by
  rw [← tripleSparseResolvent_toPolynomial a.1,
    SparseCoefficientList.coeff_toPolynomial]
  rfl

theorem pairSparseResolventCoefficient_symmetric
    (a : (Fin 2 → ℕ) × Fin 16) :
    (SparsePolynomial.toMv (pairSparseResolventCoefficient a)).IsSymmetric := by
  rw [pairSparseResolventCoefficient_toMv]
  exact pairUniversalEvaluatedResolvent_coefficient_isSymmetric a.1 a.2

theorem tripleSparseResolventCoefficient_symmetric
    (a : (Fin 2 → ℕ) × Fin 11) :
    (SparsePolynomial.toMv
      (tripleSparseResolventCoefficient a)).IsSymmetric := by
  rw [tripleSparseResolventCoefficient_toMv]
  exact tripleUniversalEvaluatedResolvent_coefficient_isSymmetric a.1 a.2

/-! ## Recursiveness of the actual resolvent coefficients -/

namespace SparseCoefficientList

theorem add_primrec : Primrec₂ SparseCoefficientList.add := by
  change Primrec fun p : SparseCoefficientList × SparseCoefficientList ↦
    SparseCoefficientList.add p.1 p.2
  have hlength : Primrec fun p : SparseCoefficientList ×
      SparseCoefficientList ↦ max p.1.length p.2.length :=
    Primrec.nat_max.comp
      (Primrec.list_length.comp Primrec.fst)
      (Primrec.list_length.comp Primrec.snd)
  apply (Primrec.list_map (Primrec.list_range.comp hlength) ?_).of_eq
    (fun _ ↦ rfl)
  change Primrec₂ fun p : SparseCoefficientList × SparseCoefficientList ↦
      fun n : ℕ ↦
        SparsePolynomial.add (p.1.getD n []) (p.2.getD n [])
  exact SparsePolynomial.add_primrec.comp
    ((Primrec.list_getD ([] : SparsePolynomial)).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd)
    ((Primrec.list_getD ([] : SparsePolynomial)).comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd)

theorem scale_primrec : Primrec₂ SparseCoefficientList.scale := by
  change Primrec fun p : SparsePolynomial × SparseCoefficientList ↦
    p.2.map (SparsePolynomial.mul p.1)
  apply Primrec.list_map Primrec.snd
  change Primrec₂ fun p : SparsePolynomial × SparseCoefficientList ↦
      fun b : SparsePolynomial ↦ SparsePolynomial.mul p.1 b
  exact SparsePolynomial.mul_primrec.comp
    (Primrec.fst.comp Primrec.fst) Primrec.snd

theorem shift_primrec : Primrec SparseCoefficientList.shift := by
  exact Primrec.list_cons.comp (Primrec.const []) Primrec.id

theorem linearProduct_primrec :
    Primrec SparseCoefficientList.linearProduct := by
  have hstep : Primrec₂ fun _roots : List SparsePolynomial ↦
      fun u : SparsePolynomial × List SparsePolynomial ×
          SparseCoefficientList ↦
        SparseCoefficientList.add
          (SparseCoefficientList.scale (SparsePolynomial.neg u.1) u.2.2)
          (SparseCoefficientList.shift u.2.2) := by
    change Primrec fun z : List SparsePolynomial ×
        (SparsePolynomial × List SparsePolynomial ×
          SparseCoefficientList) ↦
      SparseCoefficientList.add
        (SparseCoefficientList.scale (SparsePolynomial.neg z.2.1) z.2.2.2)
        (SparseCoefficientList.shift z.2.2.2)
    exact add_primrec.comp
      (scale_primrec.comp
        (SparsePolynomial.neg_primrec.comp
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (shift_primrec.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact (Primrec.list_rec Primrec.id
    (Primrec.const [SparsePolynomial.const 1]) hstep).of_eq fun roots ↦ by
      induction roots with
      | nil => rfl
      | cons a roots ih =>
          change (List.recOn roots [SparsePolynomial.const 1]
              (fun b _ IH ↦ SparseCoefficientList.add
                (SparseCoefficientList.scale (SparsePolynomial.neg b) IH)
                (SparseCoefficientList.shift IH))) =
            SparseCoefficientList.linearProduct roots at ih
          change SparseCoefficientList.add
              (SparseCoefficientList.scale (SparsePolynomial.neg a)
                (List.recOn roots [SparsePolynomial.const 1]
                  (fun b _ IH ↦ SparseCoefficientList.add
                    (SparseCoefficientList.scale (SparsePolynomial.neg b) IH)
                    (SparseCoefficientList.shift IH))))
              (SparseCoefficientList.shift
                (List.recOn roots [SparsePolynomial.const 1]
                  (fun b _ IH ↦ SparseCoefficientList.add
                    (SparseCoefficientList.scale (SparsePolynomial.neg b) IH)
                    (SparseCoefficientList.shift IH)))) =
            SparseCoefficientList.add
              (SparseCoefficientList.scale (SparsePolynomial.neg a)
                (SparseCoefficientList.linearProduct roots))
              (SparseCoefficientList.shift
                (SparseCoefficientList.linearProduct roots))
          rw [ih]

end SparseCoefficientList

theorem natConst_primrec : Primrec natConst :=
  SparsePolynomial.const_primrec.comp int_ofNat_primrec

theorem sparseParameter_primrec (i : Fin 2) :
    Primrec fun x : Fin 2 → ℕ ↦ x i :=
  Primrec.fin_app.comp Primrec.id (Primrec.const i)

theorem sparseLinearFactor_primrec (i : Fin 6) :
    Primrec fun x : Fin 2 → ℕ ↦
      SparsePolynomial.sub (natConst (x 1)) (SparsePolynomial.var i) := by
  exact SparsePolynomial.add_primrec.comp
    (natConst_primrec.comp (sparseParameter_primrec 1))
    (SparsePolynomial.neg_primrec.comp
      (Primrec.const (SparsePolynomial.var i)))

theorem pairSparseBlockValue_primrec (p : PairPartition) (b : Fin 3) :
    Primrec fun x ↦ pairSparseBlockValue x p b := by
  exact SparsePolynomial.mul_primrec.comp
    (sparseLinearFactor_primrec (pairMember p b 0))
    (sparseLinearFactor_primrec (pairMember p b 1))

theorem tripleSparseBlockValue_primrec (p : TriplePartition) (b : Fin 2) :
    Primrec fun x ↦ tripleSparseBlockValue x p b := by
  exact SparsePolynomial.mul_primrec.comp
    (sparseLinearFactor_primrec (tripleMember p b 0)) <|
    SparsePolynomial.mul_primrec.comp
      (sparseLinearFactor_primrec (tripleMember p b 1))
      (sparseLinearFactor_primrec (tripleMember p b 2))

theorem pairSparseDescriptorFactor_primrec (p : PairPartition) (b : Fin 3) :
    Primrec fun x : Fin 2 → ℕ ↦
      SparsePolynomial.sub (natConst (x 0))
        (pairSparseBlockValue x p b) := by
  exact SparsePolynomial.add_primrec.comp
    (natConst_primrec.comp (sparseParameter_primrec 0))
    (SparsePolynomial.neg_primrec.comp
      (pairSparseBlockValue_primrec p b))

theorem tripleSparseDescriptorFactor_primrec
    (p : TriplePartition) (b : Fin 2) :
    Primrec fun x : Fin 2 → ℕ ↦
      SparsePolynomial.sub (natConst (x 0))
        (tripleSparseBlockValue x p b) := by
  exact SparsePolynomial.add_primrec.comp
    (natConst_primrec.comp (sparseParameter_primrec 0))
    (SparsePolynomial.neg_primrec.comp
      (tripleSparseBlockValue_primrec p b))

theorem pairSparseDescriptorValue_primrec (p : PairPartition) :
    Primrec fun x ↦ pairSparseDescriptorValue x p := by
  exact SparsePolynomial.mul_primrec.comp
    (pairSparseDescriptorFactor_primrec p 0) <|
    SparsePolynomial.mul_primrec.comp
      (pairSparseDescriptorFactor_primrec p 1)
      (pairSparseDescriptorFactor_primrec p 2)

theorem tripleSparseDescriptorValue_primrec (p : TriplePartition) :
    Primrec fun x ↦ tripleSparseDescriptorValue x p := by
  exact SparsePolynomial.mul_primrec.comp
    (tripleSparseDescriptorFactor_primrec p 0)
    (tripleSparseDescriptorFactor_primrec p 1)

theorem pairSparseResolvent_primrec : Primrec pairSparseResolvent := by
  exact SparseCoefficientList.linearProduct_primrec.comp
    (Primrec.list_ofFn fun p ↦ pairSparseDescriptorValue_primrec p)

theorem tripleSparseResolvent_primrec : Primrec tripleSparseResolvent := by
  exact SparseCoefficientList.linearProduct_primrec.comp
    (Primrec.list_ofFn fun p ↦ tripleSparseDescriptorValue_primrec p)

theorem pairSparseResolventCoefficient_primrec :
    Primrec pairSparseResolventCoefficient := by
  exact (Primrec.list_getD ([] : SparsePolynomial)).comp
    (pairSparseResolvent_primrec.comp Primrec.fst)
    (Primrec.fin_val.comp Primrec.snd)

theorem tripleSparseResolventCoefficient_primrec :
    Primrec tripleSparseResolventCoefficient := by
  exact (Primrec.list_getD ([] : SparsePolynomial)).comp
    (tripleSparseResolvent_primrec.comp Primrec.fst)
    (Primrec.fin_val.comp Primrec.snd)

noncomputable def pairElementarySparse :
    ((Fin 2 → ℕ) × Fin 16) → SparsePolynomial :=
  elementarySparse pairSparseResolventCoefficient
    pairSparseResolventCoefficient_symmetric

noncomputable def tripleElementarySparse :
    ((Fin 2 → ℕ) × Fin 11) → SparsePolynomial :=
  elementarySparse tripleSparseResolventCoefficient
    tripleSparseResolventCoefficient_symmetric

theorem pairElementarySparse_computable : Computable pairElementarySparse :=
  elementarySparse_computable pairSparseResolventCoefficient
    pairSparseResolventCoefficient_primrec.to_comp
    pairSparseResolventCoefficient_symmetric

theorem tripleElementarySparse_computable : Computable tripleElementarySparse :=
  elementarySparse_computable tripleSparseResolventCoefficient
    tripleSparseResolventCoefficient_primrec.to_comp
    tripleSparseResolventCoefficient_symmetric

theorem pairElementarySparse_correct (a : (Fin 2 → ℕ) × Fin 16) :
    MvPolynomial.aeval
        (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
        (SparsePolynomial.toMv (pairElementarySparse a)) =
      (pairUniversalEvaluatedResolvent a.1).coeff a.2 := by
  rw [pairElementarySparse, elementarySparse_correct,
    pairSparseResolventCoefficient_toMv]

theorem tripleElementarySparse_correct (a : (Fin 2 → ℕ) × Fin 11) :
    MvPolynomial.aeval
        (fun i : Fin 6 ↦ MvPolynomial.esymm (Fin 6) ℤ (i + 1))
        (SparsePolynomial.toMv (tripleElementarySparse a)) =
      (tripleUniversalEvaluatedResolvent a.1).coeff a.2 := by
  rw [tripleElementarySparse, elementarySparse_correct,
    tripleSparseResolventCoefficient_toMv]

end SparsePolynomial

end LeanProofs.PolynomialFormulas.SexticSparseSymmetricSearch
