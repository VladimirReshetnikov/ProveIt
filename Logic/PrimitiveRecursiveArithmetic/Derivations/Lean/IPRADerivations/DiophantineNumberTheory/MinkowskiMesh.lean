import IPRADerivations.DiophantineNumberTheory.MinkowskiPigeonhole
import IPRADerivations.DiophantineNumberTheory.MinkowskiResidues

/-!
# Actual pure finite signed-mesh extraction

The runtime color count is `m^N`. The first `m^N+1` decoded signed
vectors are colored by their actual coordinate residues. Prefix pigeonhole
selects two indices; an actual sequence records their signed quotient
differences. Decoded vector distinctness supplies a coordinate witness,
which proves that the actual least nonzero-coordinate search succeeds.

This kernel takes a finite list with sufficient length and decoded
pairwise distinctness. It does not claim to derive that list or its guards
from a geometric BoxOK/grid certificate. The total entry decoder determines
the first N signed coordinates; canonical pair encodings are unnecessary.
There is no asserted zero padding: `entry a k` is literally
`fst(drop (length(a)∸(k+1)) (snd a))`, even for short/malformed codes.
A geometric producer may separately require each stored vector to have
length N. The kernel also admits N=0; its decoded-distinctness guard then
has no realizations, whereas the source public geometric theorem assumes
positive dimension.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiMesh

open_ipra exports
open LeanProofs.IPRA.Foundations.MasterCertificate
  (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.DiophantineNumberTheory.SignedEuclidean
  (decode pack computedQuotient computedRemainder)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiResidues (color colorF digit)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (subst_up_shift')

variable {n : ℕ} {Γ : List (Fm PTm n)}

def horizon (N m : PTm n) : PTm n := pw m N
def data (N m L : PTm n) : PTm n := pairT N (pairT m L)
def colorBody : PTm 2 := color (fstT (var 1)) (fstT (sndT (var 1))) (entry (sndT (sndT (var 1))) (var 0))
def colorFamily : PR 2 := PTm.toPR colorBody

@[simp] theorem subst_horizon {l : ℕ} (σ : Fin n → PTm l) (N m : PTm n) :
    Syn.subst σ (horizon N m) = horizon (Syn.subst σ N) (Syn.subst σ m) := subst_ap2 _ _ _ _
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (N m L : PTm n) :
    Syn.subst σ (data N m L) = data (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ L) := by simp only [data, subst_pairT]

theorem colorFamily_at (N m L i : PTm n) :
    Γ ⊢[PRAAx] ap2 colorFamily i (data N m L) ≐ color N m (entry L i) := by
  have program := toPR_eq (Γ := Γ) colorBody ![i,data N m L]
  simp only [colorBody, MinkowskiResidues.subst_color, subst_entry, subst_fstT, subst_sndT,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] at program
  exact program.eqTrans (congrAp3 colorF (fst_pair _ _)
    ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    (entry_congr ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _)))

theorem horizon_positive (N m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le one (horizon N m) :=
  le_trans ((succ_monus_succ zero _).eqTrans (zero_le (color N m zero)))
    (MinkowskiResidues.color_range N m zero hm)

/-- No range premise is supplied: the true residue code bounds every decoded vector. -/
theorem prefix_range (N m L : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] MinkowskiPigeonhole.prefixRange colorFamily (horizon N m) (data N m L) := by
  refine .allI (.impI ?_)
  have positive : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
    simpa only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift] using hm.shift
  have ranged : Γ.map Fm.shift ⊢[PRAAx] lt
      (ap2 colorFamily (var 0) (data (Syn.shift N) (Syn.shift m) (Syn.shift L)))
      (horizon (Syn.shift N) (Syn.shift m)) :=
    lt_congr (colorFamily_at (Syn.shift N) (Syn.shift m) (Syn.shift L) (var 0)).eqSymm (.eqRefl _)
      (MinkowskiResidues.color_range (Syn.shift N) (Syn.shift m) (entry (Syn.shift L) (var 0)) positive)
  simpa only [Syn.shift, subst_data, subst_horizon] using ranged.wk

def indices (N m L : PTm n) : PTm n := ap2 (MinkowskiPigeonhole.searchF colorFamily) (horizon N m) (data N m L)
def first (N m L : PTm n) : PTm n := fstT (indices N m L)
def second (N m L : PTm n) : PTm n := sndT (indices N m L)

@[simp] theorem subst_indices {l : ℕ} (σ : Fin n → PTm l) (N m L : PTm n) :
    Syn.subst σ (indices N m L) = indices (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ L) := by
  simp only [indices, subst_ap2, subst_horizon, subst_data]
@[simp] theorem subst_first {l : ℕ} (σ : Fin n → PTm l) (N m L : PTm n) :
    Syn.subst σ (first N m L) = first (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ L) := by simp only [first, subst_fstT, subst_indices]
@[simp] theorem subst_second {l : ℕ} (σ : Fin n → PTm l) (N m L : PTm n) :
    Syn.subst σ (second N m L) = second (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ L) := by simp only [second, subst_sndT, subst_indices]

theorem indices_spec (N m L : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] lt (first N m L) (second N m L) ⋏
      (le (second N m L) (horizon N m) ⋏
        (color N m (entry L (first N m L)) ≐ color N m (entry L (second N m L)))) := by
  have found := MinkowskiPigeonhole.search_collision colorFamily (horizon N m) (data N m L)
    (horizon_positive N m hm) (prefix_range N m L hm)
  exact .andI (.andE₁ found) (.andI (.andE₁ (.andE₂ found))
    ((colorFamily_at N m L (first N m L)).eqSymm.eqTrans
      ((Prf.andE₂ (.andE₂ found)).eqTrans (colorFamily_at N m L (second N m L)))))

/-- A genuine difference of decoded coordinates, with its finite witness local. -/
def differentCoordinate (N a b : PTm n) : Fm PTm n :=
  .ex (lt (var 0) (Syn.shift N) ⋏
    neg (ZT.eq (decode (entry (Syn.shift a) (var 0))) (decode (entry (Syn.shift b) (var 0)))))

@[simp] theorem subst_differentCoordinate {l : ℕ} (σ : Fin n → PTm l) (N a b : PTm n) :
    (differentCoordinate N a b).subst σ = differentCoordinate (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [differentCoordinate, Fm.subst_ex, Fm.subst_and, subst_lt, subst_neg, ZT.subst_eq,
    SignedEuclidean.subst_decode, subst_entry, Syn.subst_var, Syn.up_zero, Syn.up_succ,
    Syn.subst_shift, Syn.shift_subst]

/-- Distinctness only on the actual first `H+1` decoded vectors. -/
def prefixDistinct (N m L : PTm n) : Fm PTm n :=
  .all (le (var 0) (horizon (Syn.shift N) (Syn.shift m)) ⟶
    .all (lt (var 0) (var 1) ⟶
      differentCoordinate (Syn.shift (Syn.shift N)) (entry (Syn.shift (Syn.shift L)) (var 0))
        (entry (Syn.shift (Syn.shift L)) (var 1))))

@[simp] theorem subst_prefixDistinct {l : ℕ} (σ : Fin n → PTm l) (N m L : PTm n) :
    (prefixDistinct N m L).subst σ = prefixDistinct (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ L) := by
  simp only [prefixDistinct, Fm.subst_all, Fm.subst_imp, subst_le, subst_lt, subst_horizon,
    subst_differentCoordinate, subst_entry, Syn.subst_var, Syn.up_zero, Syn.up_one, Syn.up_succ,
    Syn.subst_shift, Syn.shift_subst, Syn.shift_var, Fin.succ_zero_eq_one]

theorem distinct_at (N m L i j : PTm n) (hd : Γ ⊢[PRAAx] prefixDistinct N m L)
    (hj : Γ ⊢[PRAAx] le j (horizon N m)) (hij : Γ ⊢[PRAAx] lt i j) :
    Γ ⊢[PRAAx] differentCoordinate N (entry L i) (entry L j) := by
  have first : Γ ⊢[PRAAx] le j (horizon N m) ⟶
      .all (lt (var 0) (Syn.shift j) ⟶ differentCoordinate (Syn.shift N)
        (entry (Syn.shift L) (var 0)) (entry (Syn.shift L) (Syn.shift j))) := by
    simpa only [prefixDistinct, Fm.subst_all, Fm.subst_imp, subst_le, subst_lt, subst_horizon,
      subst_differentCoordinate, subst_entry, Syn.subst_var, Syn.inst_zero, Syn.up_zero, Syn.up_one,
      Syn.up_succ, Syn.subst_inst_shift, subst_up_shift'] using Prf.allE j hd
  have contract : Γ ⊢[PRAAx] lt i j ⟶ differentCoordinate N (entry L i) (entry L j) := by
    simpa only [Fm.subst_imp, subst_lt, subst_differentCoordinate, subst_entry,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE i (Prf.impE first hj)
  exact Prf.impE contract hij

/-- Actual signed quotient difference, without normalization of its pair code. -/
def delta (a b m k : PTm n) : ZT n := computedQuotient (entry a k) m-computedQuotient (entry b k) m

@[simp] theorem subst_delta {l : ℕ} (σ : Fin n → PTm l) (a b m k : PTm n) :
    (delta a b m k).subst σ = delta (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ m) (Syn.subst σ k) := by
  simp only [delta, ZT.subst_sub, SignedEuclidean.subst_computedQuotient, subst_entry]

def vectorData (a b m : PTm n) : PTm n := pairT a (pairT b m)
def vectorBody : PTm 2 := pack (delta (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0))
def quotientVector (N a b m : PTm n) : PTm n := sequence vectorBody N (vectorData a b m)

@[simp] theorem subst_vectorData {l : ℕ} (σ : Fin n → PTm l) (a b m : PTm n) :
    Syn.subst σ (vectorData a b m) = vectorData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ m) := by simp only [vectorData, subst_pairT]
@[simp] theorem subst_quotientVector {l : ℕ} (σ : Fin n → PTm l) (N a b m : PTm n) :
    Syn.subst σ (quotientVector N a b m) = quotientVector (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ m) := by
  simp only [quotientVector, subst_sequence, subst_vectorData]

theorem quotientVector_length (N a b m : PTm n) : Γ ⊢[PRAAx] length (quotientVector N a b m) ≐ N := sequence_length _ _ _

theorem vectorBody_at (a b m k : PTm n) :
    Γ ⊢[PRAAx] inst2 vectorBody k (vectorData a b m) ≐ pack (delta a b m k) := by
  have h := Prf.eqCongr (Γ := Γ) (pack (delta (var 0) (var 1) (var 2) (var 3)) : PTm 4)
    (σ := ![fstT (vectorData a b m),fstT (sndT (vectorData a b m)),sndT (sndT (vectorData a b m)),k])
    (σ' := ![a,b,m,k]) (fun i => by
      fin_cases i
      · exact fst_pair _ _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
  simpa only [vectorBody, inst2, SignedEuclidean.subst_pack, subst_delta, subst_fstT, subst_sndT,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] using h

theorem quotientVector_lookup (N a b m k : PTm n) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] entry (quotientVector N a b m) k ≐ pack (delta a b m k) :=
  (sequence_decode vectorBody hk).eqTrans (vectorBody_at a b m k)

theorem quotientVector_value (N a b m k : PTm n) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] ZT.eq (decode (entry (quotientVector N a b m) k)) (delta a b m k) := by
  have e := quotientVector_lookup N a b m k hk
  apply ZT.derive
  simp only [decode, ZT.toZ]
  rw [natEq ((congrFst e).eqTrans (fst_pair _ _)),natEq ((congrSnd e).eqTrans (snd_pair _ _))]

/-- The actual vector's coordinate equation is derived from the color collision. -/
theorem quotientVector_equation (N a b m k : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hk : Γ ⊢[PRAAx] lt k N) (h : Γ ⊢[PRAAx] color N m a ≐ color N m b) :
    Γ ⊢[PRAAx] ZT.eq (decode (entry a k)-decode (entry b k))
      (ZT.ofNat m*decode (entry (quotientVector N a b m) k)) := by
  apply ZT.derive
  have equation := ZT.toZ_eq (MinkowskiResidues.collision_coordinate_difference N m a b k hm hk h)
  have value := ZT.toZ_eq (quotientVector_value N a b m k hk)
  rw [ZT.toZ_mul, value]
  simpa only [ZT.toZ_mul, delta] using equation

/-- Natural pair equality is exactly decoded zero, not inequality of raw codes. -/
theorem zero_of_equal (u : ZT n) (h : Γ ⊢[PRAAx] u.pos ≐ u.neg) :
    Γ ⊢[PRAAx] ZT.eq u (ZT.natLit 0) := by
  apply ZT.derive
  rw [ZT.toZ_natLit]
  simp only [ZT.toZ]
  rw [natEq h]
  ring

theorem equal_of_zero (u : ZT n) (h : Γ ⊢[PRAAx] ZT.eq u (ZT.natLit 0)) :
    Γ ⊢[PRAAx] u.pos ≐ u.neg := by
  apply deriveNat
  have e := ZT.toZ_eq h
  rw [ZT.toZ_natLit] at e
  simp only [ZT.toZ] at e
  linear_combination e

def test (a b m k : PTm n) : PTm n := eqb (delta a b m k).pos (delta a b m k).neg
def testBody : PTm 2 := test (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def nonzeroIndex (N a b m : PTm n) : PTm n := Search.mu testBody N (vectorData a b m)

@[simp] theorem subst_test {l : ℕ} (σ : Fin n → PTm l) (a b m k : PTm n) :
    Syn.subst σ (test a b m k) = test (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ m) (Syn.subst σ k) := by
  have e := subst_delta σ a b m k
  simp only [test, subst_eqb]
  exact congrArg₂ eqb (congrArg ZT.pos e) (congrArg ZT.neg e)

@[simp] theorem subst_nonzeroIndex {l : ℕ} (σ : Fin n → PTm l) (N a b m : PTm n) :
    Syn.subst σ (nonzeroIndex N a b m) = nonzeroIndex (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ m) := by
  simp only [nonzeroIndex, Search.mu, subst_ap2, subst_vectorData]

theorem testBody_at (a b m k : PTm n) :
    Γ ⊢[PRAAx] inst2 testBody k (vectorData a b m) ≐ test a b m k := by
  have h := Prf.eqCongr (Γ := Γ) (test (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (vectorData a b m),fstT (sndT (vectorData a b m)),sndT (sndT (vectorData a b m)),k])
    (σ' := ![a,b,m,k]) (fun i => by
      fin_cases i
      · exact fst_pair _ _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
  simpa only [testBody, inst2, subst_test, subst_fstT, subst_sndT,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] using h

theorem test_zero_of_nonzero (a b m k : PTm n) (h : Γ ⊢[PRAAx] neg (ZT.eq (delta a b m k) (ZT.natLit 0))) :
    Γ ⊢[PRAAx] test a b m k ≐ zero :=
  eqb_of_ne (.impI (.impE h.wk (zero_of_equal _ Prf.hyp0)))

theorem nonzero_of_test_zero (a b m k : PTm n) (h : Γ ⊢[PRAAx] test a b m k ≐ zero) :
    Γ ⊢[PRAAx] neg (ZT.eq (delta a b m k) (ZT.natLit 0)) := by
  refine .impI ?_
  exact succ_ne_zero ((eqb_of_eq (equal_of_zero _ Prf.hyp0)).eqSymm.eqTrans h.wk)

/-- A genuine decoded difference supplies success of the actual bounded search.
The existential source coordinate is eliminated locally and never exported. -/
theorem nonzero_search (N a b m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hcolor : Γ ⊢[PRAAx] color N m a ≐ color N m b)
    (hdiff : Γ ⊢[PRAAx] differentCoordinate N a b) :
    Γ ⊢[PRAAx] lt (nonzeroIndex N a b m) N ⋏
      neg (ZT.eq (delta a b m (nonzeroIndex N a b m)) (ZT.natLit 0)) := by
  refine .exE hdiff ?_
  let E : Fm PTm (n+1) := lt (var 0) (Syn.shift N) ⋏
    neg (ZT.eq (decode (entry (Syn.shift a) (var 0))) (decode (entry (Syn.shift b) (var 0))))
  have positive : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
    simpa only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift] using hm.shift
  have colored : Γ.map Fm.shift ⊢[PRAAx] color (Syn.shift N) (Syn.shift m) (Syn.shift a) ≐ color (Syn.shift N) (Syn.shift m) (Syn.shift b) := by
    simpa only [Fm.shift, Fm.subst_eq, MinkowskiResidues.subst_color, Syn.shift] using hcolor.shift
  have residues : E :: Γ.map Fm.shift ⊢[PRAAx]
      computedRemainder (entry (Syn.shift a) (var 0)) (Syn.shift m) ≐
        computedRemainder (entry (Syn.shift b) (var 0)) (Syn.shift m) :=
    MinkowskiResidues.coordinate_injective _ _ _ _ _ positive.wk (Prf.andE₁ Prf.hyp0) colored.wk
  have nonzero : E :: Γ.map Fm.shift ⊢[PRAAx]
      neg (ZT.eq (delta (Syn.shift a) (Syn.shift b) (Syn.shift m) (var 0)) (ZT.natLit 0)) :=
    SignedEuclidean.computed_nonzero_difference _ _ _ positive.wk residues (Prf.andE₂ Prf.hyp0)
  have zero := (testBody_at (Syn.shift a) (Syn.shift b) (Syn.shift m) (var 0)).eqTrans
    (test_zero_of_nonzero _ _ _ _ nonzero)
  have found := Search.search_found zero (Prf.andE₁ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E))
  have result : E :: Γ.map Fm.shift ⊢[PRAAx]
      lt (nonzeroIndex (Syn.shift N) (Syn.shift a) (Syn.shift b) (Syn.shift m)) (Syn.shift N) ⋏
      neg (ZT.eq (delta (Syn.shift a) (Syn.shift b) (Syn.shift m)
        (nonzeroIndex (Syn.shift N) (Syn.shift a) (Syn.shift b) (Syn.shift m))) (ZT.natLit 0)) :=
    .andI (Prf.andE₁ found) (nonzero_of_test_zero _ _ _ _
      ((testBody_at _ _ _ _).eqSymm.eqTrans (Prf.andE₁ (Prf.andE₂ found))))
  simpa only [E, Fm.shift, Fm.subst_and, subst_lt, subst_neg, ZT.subst_eq, subst_delta,
    subst_nonzeroIndex, ZT.subst_natLit, Syn.shift] using result

/-- The vector entry at the actual searched coordinate is nonzero as an integer. -/
theorem nonzero_vector_entry (N a b m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hcolor : Γ ⊢[PRAAx] color N m a ≐ color N m b)
    (hdiff : Γ ⊢[PRAAx] differentCoordinate N a b) :
    Γ ⊢[PRAAx] lt (nonzeroIndex N a b m) N ⋏
      neg (ZT.eq (decode (entry (quotientVector N a b m) (nonzeroIndex N a b m))) (ZT.natLit 0)) := by
  have found := nonzero_search N a b m hm hcolor hdiff
  refine .andI (.andE₁ found) (.impI (.impE (Prf.andE₂ found).wk ?_))
  apply ZT.derive
  have zero := ZT.toZ_eq (Prf.hyp0 : ZT.eq (decode (entry (quotientVector N a b m) (nonzeroIndex N a b m))) (ZT.natLit 0) :: Γ ⊢[PRAAx] _)
  exact (ZT.toZ_eq ((quotientVector_value N a b m (nonzeroIndex N a b m) (Prf.andE₁ found)).wk)).symm.trans zero

/-- Every coordinate equation is quantified only after the actual pair is selected. -/
def equations (N m L i j z : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    ZT.eq (decode (entry (entry (Syn.shift L) (Syn.shift i)) (var 0))-
      decode (entry (entry (Syn.shift L) (Syn.shift j)) (var 0)))
      (ZT.ofNat (Syn.shift m)*decode (entry (Syn.shift z) (var 0))))

@[simp] theorem subst_equations {l : ℕ} (σ : Fin n → PTm l) (N m L i j z : PTm n) :
    (equations N m L i j z).subst σ = equations (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ L)
      (Syn.subst σ i) (Syn.subst σ j) (Syn.subst σ z) := by
  simp only [equations, Fm.subst_all, Fm.subst_imp, subst_lt, ZT.subst_eq, ZT.subst_sub,
    ZT.subst_mul, ZT.subst_ofNat, SignedEuclidean.subst_decode, subst_entry,
    Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

def vector (N m L : PTm n) : PTm n := quotientVector N (entry L (first N m L)) (entry L (second N m L)) m
def coordinateIndex (N m L : PTm n) : PTm n := nonzeroIndex N (entry L (first N m L)) (entry L (second N m L)) m

def good (N m L i j z k : PTm n) : Fm PTm n :=
  lt i j ⋏ (le j (horizon N m) ⋏ (lt j (length L) ⋏ (lt i (length L) ⋏
    ((length z ≐ N) ⋏ (equations N m L i j z ⋏ (lt k N ⋏
      neg (ZT.eq (decode (entry z k)) (ZT.natLit 0))))))))

@[simp] theorem subst_good {l : ℕ} (σ : Fin n → PTm l) (N m L i j z k : PTm n) :
    (good N m L i j z k).subst σ = good (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ L)
      (Syn.subst σ i) (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ k) := by
  simp only [good, Fm.subst_and, Fm.subst_eq, subst_lt, subst_le, subst_horizon, subst_length,
    subst_equations, subst_neg, ZT.subst_eq, SignedEuclidean.subst_decode, subst_entry, ZT.subst_natLit]

/-- Correctness of the concrete selected indices, computed vector and searched coordinate. -/
theorem mesh_good (N m L : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hL : Γ ⊢[PRAAx] le (succ (horizon N m)) (length L))
    (hd : Γ ⊢[PRAAx] prefixDistinct N m L) :
    Γ ⊢[PRAAx] good N m L (first N m L) (second N m L) (vector N m L) (coordinateIndex N m L) := by
  have spec := indices_spec N m L hm
  have different := distinct_at N m L (first N m L) (second N m L) hd (Prf.andE₁ (Prf.andE₂ spec)) (Prf.andE₁ spec)
  have nonzero := nonzero_vector_entry N (entry L (first N m L)) (entry L (second N m L)) m hm
    (Prf.andE₂ (Prf.andE₂ spec)) different
  have jL : Γ ⊢[PRAAx] lt (second N m L) (length L) :=
    le_trans ((succ_monus_succ _ _).eqTrans (Prf.andE₁ (Prf.andE₂ spec))) hL
  have iL := lt_of_lt_of_le (Prf.andE₁ spec) (le_of_lt jL)
  have coordinate_equations : Γ ⊢[PRAAx] equations N m L (first N m L) (second N m L) (vector N m L) := by
    refine .allI (.impI ?_)
    have positive : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
      simpa only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift] using hm.shift
    have colored : Γ.map Fm.shift ⊢[PRAAx] color (Syn.shift N) (Syn.shift m)
        (entry (Syn.shift L) (Syn.shift (first N m L))) ≐
        color (Syn.shift N) (Syn.shift m) (entry (Syn.shift L) (Syn.shift (second N m L))) := by
      simpa only [Fm.shift, Fm.subst_eq, MinkowskiResidues.subst_color, subst_entry, Syn.shift] using
        (Prf.andE₂ (Prf.andE₂ spec)).shift
    have equation := quotientVector_equation (Syn.shift N)
      (entry (Syn.shift L) (Syn.shift (first N m L))) (entry (Syn.shift L) (Syn.shift (second N m L)))
      (Syn.shift m) (var 0) positive.wk (Prf.hyp0 : lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx] _) colored.wk
    simpa only [vector, Syn.shift, subst_quotientVector, subst_entry] using equation
  exact .andI (Prf.andE₁ spec) (.andI (Prf.andE₁ (Prf.andE₂ spec)) (.andI jL (.andI iL
    (.andI (quotientVector_length _ _ _ _) (.andI coordinate_equations nonzero)))))


@[simp] theorem subst_vector {l : ℕ} (σ : Fin n → PTm l) (N m L : PTm n) :
    Syn.subst σ (vector N m L) = vector (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ L) := by
  simp only [vector, subst_quotientVector, subst_entry, subst_first, subst_second]
@[simp] theorem subst_coordinateIndex {l : ℕ} (σ : Fin n → PTm l) (N m L : PTm n) :
    Syn.subst σ (coordinateIndex N m L) = coordinateIndex (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ L) := by
  simp only [coordinateIndex, subst_nonzeroIndex, subst_entry, subst_first, subst_second]

/-- Concrete output: pair of indices, followed by the quotient vector and least
nonzero coordinate. All three inputs are persistent numerical parameters. -/
def result (N m L : PTm n) : PTm n :=
  pairT (indices N m L) (pairT (vector N m L) (coordinateIndex N m L))
def meshF : PR 3 := PTm.toPR (result (var 0) (var 1) (var 2))

@[simp] theorem subst_result {l : ℕ} (σ : Fin n → PTm l) (N m L : PTm n) :
    Syn.subst σ (result N m L) = result (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ L) := by
  simp only [result, subst_pairT, subst_indices, subst_vector, subst_coordinateIndex]

theorem mesh_at (N m L : PTm n) :
    Γ ⊢[PRAAx] ap3 meshF N m L ≐ result N m L := by
  have h := toPR_eq (Γ := Γ) (result (var 0) (var 1) (var 2) : PTm 3) ![N,m,L]
  simpa only [meshF, ap3, subst_result, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

/-- The specification refers to the fields of the actual returned code. -/
def correct (N m L c : PTm n) : Fm PTm n :=
  good N m L (fstT (fstT c)) (sndT (fstT c)) (fstT (sndT c)) (sndT (sndT c))

@[simp] theorem subst_correct {l : ℕ} (σ : Fin n → PTm l) (N m L c : PTm n) :
    (correct N m L c).subst σ = correct (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ c) := by
  simp only [correct, subst_good, subst_fstT, subst_sndT]

theorem good_congr (N m L i j z k i' j' z' k' : PTm n)
    (hi : Γ ⊢[PRAAx] i ≐ i') (hj : Γ ⊢[PRAAx] j ≐ j')
    (hz : Γ ⊢[PRAAx] z ≐ z') (hk : Γ ⊢[PRAAx] k ≐ k')
    (h : Γ ⊢[PRAAx] good N m L i j z k) : Γ ⊢[PRAAx] good N m L i' j' z' k' := by
  have e5 : (5 : Fin 7) = (4 : Fin 6).succ := rfl
  have e6 : (6 : Fin 7) = (5 : Fin 6).succ := rfl
  have e5' : (5 : Fin 6) = (4 : Fin 5).succ := rfl
  have input : Γ ⊢[PRAAx]
      (good (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)).subst ![N,m,L,i,j,z,k] := by
    simpa only [subst_good, Syn.subst_var, e5, e6, e5', Matrix.cons_val_succ, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] using h
  have output := Prf.eqSubst
    (good (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
    ![N,m,L,i,j,z,k] ![N,m,L,i',j',z',k']
    (fun a => by fin_cases a <;> first | exact hi | exact hj | exact hz | exact hk | exact .eqRefl _) input
  simpa only [subst_good, Syn.subst_var, e5, e6, e5', Matrix.cons_val_succ, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] using output

theorem result_correct (N m L : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hL : Γ ⊢[PRAAx] le (succ (horizon N m)) (length L))
    (hd : Γ ⊢[PRAAx] prefixDistinct N m L) :
    Γ ⊢[PRAAx] correct N m L (result N m L) :=
  good_congr N m L _ _ _ _ _ _ _ _
    (congrFst (fst_pair _ _)).eqSymm (congrSnd (fst_pair _ _)).eqSymm
    ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)).eqSymm
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)).eqSymm
    (mesh_good N m L hm hL hd)

/-- The executable primitive-recursive mesh extractor is correct under only the
finite decoded-distinctness and list-length guards. In particular neither a
color collision nor a nonzero quotient coordinate is a supplied premise. -/
theorem mesh_correct (N m L : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hL : Γ ⊢[PRAAx] le (succ (horizon N m)) (length L))
    (hd : Γ ⊢[PRAAx] prefixDistinct N m L) :
    Γ ⊢[PRAAx] correct N m L (ap3 meshF N m L) :=
  good_congr N m L _ _ _ _ _ _ _ _
    (congrFst (congrFst (mesh_at N m L))).eqSymm
    (congrSnd (congrFst (mesh_at N m L))).eqSymm
    (congrFst (congrSnd (mesh_at N m L))).eqSymm
    (congrSnd (congrSnd (mesh_at N m L))).eqSymm
    (result_correct N m L hm hL hd)

/-- Fully closed correctness at arbitrary runtime dimension, modulus and list. -/
theorem mesh_correct_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le one (var 1) ⟶ le (succ (horizon (var 0) (var 1))) (length (var 2)) ⟶
        prefixDistinct (var 0) (var 1) (var 2) ⟶
          correct (var 0) (var 1) (var 2) (ap3 meshF (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (mesh_correct _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

/-- Closed program metadata exposes the literal paired construction. -/
theorem mesh_program_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ap3 meshF (var 0) (var 1) (var 2) ≐ result (var 0) (var 1) (var 2)) :=
  closeUniv 3 (mesh_at _ _ _)

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiMesh
