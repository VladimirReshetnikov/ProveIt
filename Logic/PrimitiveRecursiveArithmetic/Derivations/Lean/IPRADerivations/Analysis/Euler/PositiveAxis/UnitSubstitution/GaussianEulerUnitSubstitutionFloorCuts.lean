import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionTiltedNodes
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianEulerUnitDecayInput
import IPRADerivations.Analysis.RationalArithmetic.Grids.RationalUnitFloorBounds
import IPRADerivations.Analysis.Integration.Partitions.GaussianPartitionedFiniteSum

/-!
# Actual bounded integer cuts of the unchanged original unit chart

The decay query retains an arbitrary base precision. A numerical guard
pays the entire tilt; every true original compact margin is then preserved
at half its size. Actual quotient cuts and all native positions between
successive cuts lie in one fixed positive unit compact. The cut program
is extended constantly after the original finite horizon.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionFloorCuts

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionTiltedNodes (correctedNode reverseNode)
open RationalNonnegativeFloor (index)
open RationalConvexSecants (naturalNumerator nonnegative)
open RationalSupMetric (numeratorOf denominatorOf)
open GaussianRationalHorner (positive_product scalar_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerUnitDecayInput (compactDenominator clock)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def capped (i N : PTm n) : PTm n := monus N (monus N i)
def node (i k N a C E T : PTm n) : PTm n := correctedNode (capped i N) (clock k E T) N a C E
def cut (i k N a C E T M : PTm n) : PTm n := index (node i k N a C E T) M
def relativeCut (i k N a C E T M : PTm n) : PTm n := monus (cut i k N a C E T M) (cut zero k N a C E T M)
def source (k N a C E T M : PTm n) : Fm PTm n :=
  (le one a ⋏ (le one E ⋏ (le one T ⋏ le (a+C) (E*T)))) ⋏
    (le one N ⋏ (le ((two*two)*compactDenominator E T*N) (unit (clock k E T)) ⋏
      le (two*(two*compactDenominator E T)) M))

@[simp] theorem subst_capped {m : ℕ} (σ : Fin n → PTm m) (i N : PTm n) :
    Syn.subst σ (capped i N) = capped (Syn.subst σ i) (Syn.subst σ N) := by simp [capped]
@[simp] theorem subst_node {m : ℕ} (σ : Fin n → PTm m) (i k N a C E T : PTm n) :
    Syn.subst σ (node i k N a C E T) = node (Syn.subst σ i) (Syn.subst σ k) (Syn.subst σ N)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [node]
@[simp] theorem subst_cut {m : ℕ} (σ : Fin n → PTm m) (i k N a C E T M : PTm n) :
    Syn.subst σ (cut i k N a C E T M) = cut (Syn.subst σ i) (Syn.subst σ k) (Syn.subst σ N)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by simp [cut]
@[simp] theorem subst_relativeCut {m : ℕ} (σ : Fin n → PTm m) (i k N a C E T M : PTm n) :
    Syn.subst σ (relativeCut i k N a C E T M) = relativeCut (Syn.subst σ i) (Syn.subst σ k) (Syn.subst σ N)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by simp [relativeCut]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (k N a C E T M : PTm n) :
    (source k N a C E T M).subst σ = source (Syn.subst σ k) (Syn.subst σ N) (Syn.subst σ a)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by simp [source]

theorem capped_below (i N : PTm n) (h : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] capped i N ≐ i := by
  have e := eq_add_of_le h
  exact (congrMonus e (.eqRefl _)).eqTrans
    (((congrMonus (.eqRefl _) (zero_add _).eqSymm).eqTrans (monus_add_add i zero _)).eqTrans (monus_zero i))

theorem capped_above (i N : PTm n) (h : Γ ⊢[PRAAx] le N i) : Γ ⊢[PRAAx] capped i N ≐ N :=
  (congrMonus (.eqRefl N) h).eqTrans (monus_zero N)

theorem capped_bound (i N : PTm n) : Γ ⊢[PRAAx] le (capped i N) N := by
  refine .orE (le_total i N) ?_ ?_
  · exact le_congr (capped_below i N Prf.hyp0).eqSymm (.eqRefl _) Prf.hyp0
  · exact le_congr (capped_above i N Prf.hyp0).eqSymm (.eqRefl _) (le_refl N)

theorem node_below (i k N a C E T : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    node i k N a C E T ≐ correctedNode i (clock k E T) N a C E := by
  simpa [node] using Prf.eqCongr1 (correctedNode (var 0) (Syn.shift (clock k E T)) (Syn.shift N) (Syn.shift a) (Syn.shift C) (Syn.shift E)) (capped_below i N hi)

theorem node_above (i k N a C E T : PTm n) (hi : Γ ⊢[PRAAx] le N i) : Γ ⊢[PRAAx]
    node i k N a C E T ≐ correctedNode N (clock k E T) N a C E := by
  simpa [node] using Prf.eqCongr1 (correctedNode (var 0) (Syn.shift (clock k E T)) (Syn.shift N) (Syn.shift a) (Syn.shift C) (Syn.shift E)) (capped_above i N hi)

private theorem scalar_source_congr {q r G : PTm n} (e : Γ ⊢[PRAAx] q ≐ r)
    (h : Γ ⊢[PRAAx] RationalUnitFloorBounds.source q G) : Γ ⊢[PRAAx] RationalUnitFloorBounds.source r G := by
  simpa using Prf.eqSubst1 (Ax := PRAAx) (Γ := Γ)
    (RationalUnitFloorBounds.source (var 0) (Syn.shift G)) e (by simpa using h)

private theorem scalar_rep_from_order (q : PTm n) (h : Γ ⊢[PRAAx] le (numeratorOf q).neg (numeratorOf q).pos) : Γ ⊢[PRAAx]
    RationalArithmetic.represents q (ZT.ofNat (naturalNumerator q)) (denominatorOf q) := by
  have e := natEq (eq_add_of_le h)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ,naturalNumerator]
  ipra_simps
  linear_combination -𝔞 (denominatorOf q)*e

private theorem original_unit_source (i k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source k N a C E T M)
    (_hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    GaussianUnitIntervalInputDecoding.source
      (GaussianEulerUnitSubstitutionImageGrid.node (monus N i) (clock k E T) N a C E) (compactDenominator E T) := by
  let j := monus N i
  let a' := a*N+C*j
  let b' := E*N
  have hj : Γ ⊢[PRAAx] le j N := GaussianRationalMonicReconstruction.monus_le_left _ _
  have ht : Γ ⊢[PRAAx] GaussianEulerUnitDecayInput.source a' b' E T := by
    refine .andI (positive_product _ _ hs.andE₁.andE₂.andE₁ hs.andE₂.andE₁)
      (.andI hs.andE₁.andE₂.andE₁ (.andI hs.andE₁.andE₂.andE₂.andE₁ (.andI ?_ ?_)))
    · dsimp only [a',b',j]
      ipra_le 𝔞 (E*N)*sl hs.andE₁.andE₁ + 𝔞 (E*C*monus N i)
    · dsimp only [a',b',j] at hj ⊢
      ipra_le 𝔞 N*sl hs.andE₁.andE₂.andE₂.andE₂ + 𝔞 C*sl hj
  have h := GaussianEulerUnitDecayInput.observation_source k a' b' E T ht
  simpa [GaussianEulerUnitSubstitutionImageGrid.node,GaussianEulerDecayMesh.observation,a',b',j] using
    Prf.eqSubst1 (Ax := PRAAx) (Γ := Γ)
      (GaussianUnitIntervalInputDecoding.source (var 0) (Syn.shift (compactDenominator E T)))
      (GaussianEulerUnitDecayInput.sample_at k a' b' E T) (by simpa using h)

theorem original_scalar_source (i k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source k N a C E T M)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    RationalUnitFloorBounds.source (reverseNode i (clock k E T) N a C E) (compactDenominator E T) := by
  have h := original_unit_source i k N a C E T M hs hi
  exact .andI h.andE₂.andE₁ (.andI (GaussianUnitIntervalInputDecoding.decoded_lower _ _ h)
    (GaussianUnitIntervalInputDecoding.decoded_upper _ _ h))

private theorem corrected_representation (i k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source k N a C E T M)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (correctedNode i (clock k E T) N a C E)
      (ZT.ofNat (unit (clock k E T)*naturalNumerator (reverseNode i (clock k E T) N a C E)+two*i*denominatorOf (reverseNode i (clock k E T) N a C E)))
      (denominatorOf (reverseNode i (clock k E T) N a C E)*unit (clock k E T)) := by
  let q := reverseNode i (clock k E T) N a C E
  have rep := RationalRepresentations.represents_add q (GaussianEuclideanDistanceName.fraction (two*i) (unit (clock k E T)))
    _ _ _ _ (scalar_rep_from_order q (GaussianUnitIntervalInputDecoding.numerator_order _ _ (original_unit_source i k N a C E T M hs hi)))
    (GaussianEuclideanDistanceName.fraction_represents _ _ (unit_positive _))
  refine scalar_congr (.eqRefl _) ?_ (.eqRefl _) rep
  ipra_ring

theorem corrected_scalar_source (i k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source k N a C E T M)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    RationalUnitFloorBounds.source (correctedNode i (clock k E T) N a C E) (two*compactDenominator E T) := by
  let q := reverseNode i (clock k E T) N a C E
  let D := denominatorOf q
  let U := unit (clock k E T)
  let V := naturalNumerator q
  let G := compactDenominator E T
  have old := original_scalar_source i k N a C E T M hs hi
  have budget : Γ ⊢[PRAAx] le ((two*two)*G*i) U :=
    le_trans (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right ((two*two)*G) hi)) hs.andE₂.andE₂.andE₁
  apply RationalUnitFloorBounds.from_representation _ (U*V+two*i*D) (D*U) (two*G)
    (positive_product _ _ (RationalArgmin.denominator_positive q) (unit_positive _))
    (le_trans old.andE₁ (le_of_eq_add (d := G) (by ipra_ring)))
    (corrected_representation i k N a C E T M hs hi)
  · have low : Γ ⊢[PRAAx] le D (G*V) := old.andE₂.andE₁
    ipra_le 2*𝔞 U*sl low + 𝔞 (D*U)+𝔞 ((two*two)*G*i*D)
  · have up : Γ ⊢[PRAAx] le (G*V+D) (G*D) := old.andE₂.andE₂
    ipra_le 2*𝔞 U*sl up + 𝔞 D*sl budget

theorem node_source (i k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source k N a C E T M) : Γ ⊢[PRAAx]
    RationalUnitFloorBounds.source (node i k N a C E T) (two*compactDenominator E T) :=
  corrected_scalar_source (capped i N) k N a C E T M hs (capped_bound i N)

theorem original_cut_source (i k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source k N a C E T M) : Γ ⊢[PRAAx]
    GaussianEulerUnitCompactTimeBounds.source (cut i k N a C E T M) M (two*(two*compactDenominator E T)) :=
  RationalUnitFloorBounds.native_source _ _ _ (node_source i k N a C E T M hs) hs.andE₂.andE₂.andE₂

theorem original_block_source (i j k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source k N a C E T M)
    (hLeft : Γ ⊢[PRAAx] le (cut i k N a C E T M) j)
    (hRight : Γ ⊢[PRAAx] le j (cut (succ i) k N a C E T M)) : Γ ⊢[PRAAx]
    GaussianEulerUnitCompactTimeBounds.source j M (two*(two*compactDenominator E T)) :=
  RationalUnitFloorBounds.block_native_source _ _ _ _ _ (node_source i k N a C E T M hs)
    (node_source (succ i) k N a C E T M hs) hs.andE₂.andE₂.andE₂ hLeft hRight


theorem node_nonnegative (i k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source k N a C E T M) : Γ ⊢[PRAAx]
    nonnegative (node i k N a C E T) :=
  GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (le_refl one)
    (positive_product _ _ (RationalArgmin.denominator_positive _) (unit_positive _))
    (GaussianRationalSyntheticBounds.natCode_represents zero)
    (corrected_representation (capped i N) k N a C E T M hs (capped_bound i N))
    (le_of_eq_add (d := unit (clock k E T)*naturalNumerator (reverseNode (capped i N) (clock k E T) N a C E)+two*(capped i N)*denominatorOf (reverseNode (capped i N) (clock k E T) N a C E)) (by ipra_ring))

theorem original_cut_step (i k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source k N a C E T M) : Γ ⊢[PRAAx]
    le (cut i k N a C E T M) (cut (succ i) k N a C E T M) := by
  apply RationalNonnegativeFloor.index_monotone _ _ _ (node_nonnegative i k N a C E T M hs)
    (node_nonnegative (succ i) k N a C E T M hs)
  refine .orE (lt_or_le i N) ?_ ?_
  · have hi : (lt i N)::Γ ⊢[PRAAx] lt i N := Prf.hyp0
    exact RationalArgmin.rationalLE_congr (node_below i k N a C E T (le_of_lt hi)).eqSymm
      (node_below (succ i) k N a C E T hi).eqSymm
      (GaussianEulerUnitSubstitutionTiltedNodes.original_corrected_order i (clock k E T) N a C E
        hs.wk.andE₁.andE₂.andE₁ hs.wk.andE₂.andE₁ hi)
  · have hi : (le N i)::Γ ⊢[PRAAx] le N i := Prf.hyp0
    exact RationalArgmin.rationalLE_congr (node_above i k N a C E T hi).eqSymm
      (node_above (succ i) k N a C E T (le_trans hi (le_succ_self i))).eqSymm (le_refl _)

theorem original_constant_extension (i k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] le N i) : Γ ⊢[PRAAx]
    cut i k N a C E T M ≐ cut N k N a C E T M := by
  have e := (node_above i k N a C E T hs).eqTrans (node_below N k N a C E T (le_refl N)).eqSymm
  simpa [cut] using Prf.eqCongr1 (index (var 0) (Syn.shift M)) e

private theorem monus_monotone (a b c : PTm n) (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (monus a c) (monus b c) := by
  refine .orE (le_total a c) ?_ ?_
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le _)
  · have ea := (eq_add_of_le (Prf.hyp0 : (le c a)::Γ ⊢[PRAAx] le c a)).eqTrans (add_comm _ _)
    have eb := (eq_add_of_le (le_trans (Prf.hyp0 : (le c a)::Γ ⊢[PRAAx] le c a) h.wk)).eqTrans (add_comm _ _)
    exact le_of_add_le_add_right (le_congr ea eb h.wk)

theorem original_relative_step (i k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source k N a C E T M) : Γ ⊢[PRAAx]
    le (relativeCut i k N a C E T M) (relativeCut (succ i) k N a C E T M) :=
  monus_monotone _ _ _ (original_cut_step i k N a C E T M hs)

def data (k N a C E T M : PTm n) : PTm n := pairT (pairT k N) (pairT (pairT a C) (pairT (pairT E T) M))
private def fields (x : PTm n) : Fin 7 → PTm n :=
  ![fstT (fstT x),sndT (fstT x),fstT (fstT (sndT x)),sndT (fstT (sndT x)),
    fstT (fstT (sndT (sndT x))),sndT (fstT (sndT (sndT x))),sndT (sndT (sndT x))]
private def absoluteReader (i x : PTm n) : PTm n :=
  cut i (fields x 0) (fields x 1) (fields x 2) (fields x 3) (fields x 4) (fields x 5) (fields x 6)
def absoluteF : PR 2 := PTm.toPR (absoluteReader (var 0) (var 1))
def cutF : PR 2 := PTm.toPR (monus (ap2 absoluteF (var 0) (var 1)) (ap2 absoluteF zero (var 1)))

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (k N a C E T M : PTm n) :
    Syn.subst σ (data k N a C E T M) = data (Syn.subst σ k) (Syn.subst σ N) (Syn.subst σ a)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by simp [data]

private theorem fields_at (k N a C E T M : PTm n) (j : Fin 7) : Γ ⊢[PRAAx]
    fields (data k N a C E T M) j ≐ (![k,N,a,C,E,T,M] : Fin 7 → PTm n) j := by
  fin_cases j
  · exact (congrFst (fst_pair _ _)).eqTrans (fst_pair k N)
  · exact (congrSnd (fst_pair _ _)).eqTrans (snd_pair k N)
  · exact (congrFst (congrFst (snd_pair _ _))).eqTrans ((congrFst (fst_pair _ _)).eqTrans (fst_pair a C))
  · exact (congrSnd (congrFst (snd_pair _ _))).eqTrans ((congrSnd (fst_pair _ _)).eqTrans (snd_pair a C))
  · exact (congrFst (congrFst (congrSnd (snd_pair _ _)))).eqTrans
      ((congrFst (congrFst (snd_pair _ _))).eqTrans ((congrFst (fst_pair _ _)).eqTrans (fst_pair E T)))
  · exact (congrSnd (congrFst (congrSnd (snd_pair _ _)))).eqTrans
      ((congrSnd (congrFst (snd_pair _ _))).eqTrans ((congrSnd (fst_pair _ _)).eqTrans (snd_pair E T)))
  · exact (congrSnd (congrSnd (snd_pair _ _))).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ M))

private theorem cut_congr {i k N a C E T M i' k' N' a' C' E' T' M' : PTm n}
    (hi : Γ ⊢[PRAAx] i ≐ i') (hk : Γ ⊢[PRAAx] k ≐ k') (hN : Γ ⊢[PRAAx] N ≐ N')
    (ha : Γ ⊢[PRAAx] a ≐ a') (hC : Γ ⊢[PRAAx] C ≐ C') (hE : Γ ⊢[PRAAx] E ≐ E')
    (hT : Γ ⊢[PRAAx] T ≐ T') (hM : Γ ⊢[PRAAx] M ≐ M') : Γ ⊢[PRAAx]
    cut i k N a C E T M ≐ cut i' k' N' a' C' E' T' M' := by
  have fieldEquality := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (cut (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8)
    (σ := ![i,k,N,a,C,E,T,M]) (σ' := ![i',k',N',a',C',E',T',M'])
    (fun j => by fin_cases j; exact hi; exact hk; exact hN; exact ha; exact hC; exact hE; exact hT; exact hM)
  have leftDecode : Syn.subst (![i,k,N,a,C,E,T,M] : Fin 8 → PTm n)
      (cut (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) = cut i k N a C E T M := by
    simp only [subst_cut,Syn.subst_var]
    rfl
  have rightDecode : Syn.subst (![i',k',N',a',C',E',T',M'] : Fin 8 → PTm n)
      (cut (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) = cut i' k' N' a' C' E' T' M' := by
    simp only [subst_cut,Syn.subst_var]
    rfl
  rw [leftDecode,rightDecode] at fieldEquality
  exact fieldEquality

theorem original_absolute_at (i k N a C E T M : PTm n) : Γ ⊢[PRAAx]
    ap2 absoluteF i (data k N a C E T M) ≐ cut i k N a C E T M := by
  have decode : Syn.subst (![i,data k N a C E T M] : Fin 2 → PTm n) (absoluteReader (var 0) (var 1)) =
      absoluteReader i (data k N a C E T M) := by simp [absoluteReader,fields]
  have compiled : Γ ⊢[PRAAx] ap2 absoluteF i (data k N a C E T M) ≐ absoluteReader i (data k N a C E T M) := by
    simpa only [absoluteF,ap2,decode] using toPR_eq (Γ := Γ) (absoluteReader (var 0) (var 1) : PTm 2) ![i,data k N a C E T M]
  exact compiled.eqTrans (cut_congr (.eqRefl _) (fields_at _ _ _ _ _ _ _ 0) (fields_at _ _ _ _ _ _ _ 1)
    (fields_at _ _ _ _ _ _ _ 2) (fields_at _ _ _ _ _ _ _ 3) (fields_at _ _ _ _ _ _ _ 4)
    (fields_at _ _ _ _ _ _ _ 5) (fields_at _ _ _ _ _ _ _ 6))

theorem original_at (i k N a C E T M : PTm n) : Γ ⊢[PRAAx]
    ap2 cutF i (data k N a C E T M) ≐ relativeCut i k N a C E T M := by
  have compiled := toPR_eq (Γ := Γ) (monus (ap2 absoluteF (var 0) (var 1)) (ap2 absoluteF zero (var 1)) : PTm 2) ![i,data k N a C E T M]
  have e : Γ ⊢[PRAAx] ap2 cutF i (data k N a C E T M) ≐
      monus (ap2 absoluteF i (data k N a C E T M)) (ap2 absoluteF zero (data k N a C E T M)) := by
    have decode : Syn.subst (![i,data k N a C E T M] : Fin 2 → PTm n)
        (monus (ap2 absoluteF (var 0) (var 1)) (ap2 absoluteF zero (var 1))) =
        monus (ap2 absoluteF i (data k N a C E T M)) (ap2 absoluteF zero (data k N a C E T M)) := by
      simp only [PTm.subst_monus,subst_ap2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,PTm.subst_zero]
    rw [decode] at compiled
    simpa only [cutF,ap2] using compiled
  exact e.eqTrans (congrMonus (original_absolute_at i k N a C E T M) (original_absolute_at zero k N a C E T M))

theorem original_zero (k N a C E T M : PTm n) : Γ ⊢[PRAAx] ap2 cutF zero (data k N a C E T M) ≐ zero :=
  (original_at zero k N a C E T M).eqTrans (monus_self _)

theorem original_absolute_increasing (k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source k N a C E T M) : Γ ⊢[PRAAx]
    GaussianPartitionedFiniteSum.increasing absoluteF (data k N a C E T M) := by
  let sh (t : PTm n) : PTm (n+1) := Syn.shift t
  have h : Γ.map Fm.shift ⊢[PRAAx] source (sh k) (sh N) (sh a) (sh C) (sh E) (sh T) (sh M) := by
    simpa [Fm.shift,Syn.shift,sh] using hs.shift
  refine .allI ?_
  simpa only [GaussianPartitionedFiniteSum.increasing,subst_data,Syn.shift,sh] using le_congr
    (original_absolute_at (var 0) (sh k) (sh N) (sh a) (sh C) (sh E) (sh T) (sh M)).eqSymm
    (original_absolute_at (succ (var 0)) (sh k) (sh N) (sh a) (sh C) (sh E) (sh T) (sh M)).eqSymm
    (original_cut_step (var 0) (sh k) (sh N) (sh a) (sh C) (sh E) (sh T) (sh M) h)

theorem original_increasing (k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source k N a C E T M) : Γ ⊢[PRAAx]
    GaussianPartitionedFiniteSum.increasing cutF (data k N a C E T M) := by
  let sh (t : PTm n) : PTm (n+1) := Syn.shift t
  have h : Γ.map Fm.shift ⊢[PRAAx] source (sh k) (sh N) (sh a) (sh C) (sh E) (sh T) (sh M) := by
    simpa [Fm.shift,Syn.shift,sh] using hs.shift
  refine .allI ?_
  simpa only [GaussianPartitionedFiniteSum.increasing,subst_data,Syn.shift,sh] using le_congr
    (original_at (var 0) (sh k) (sh N) (sh a) (sh C) (sh E) (sh T) (sh M)).eqSymm
    (original_at (succ (var 0)) (sh k) (sh N) (sh a) (sh C) (sh E) (sh T) (sh M)).eqSymm
    (original_relative_step (var 0) (sh k) (sh N) (sh a) (sh C) (sh E) (sh T) (sh M) h)

theorem actual_original_floor_cuts_unit_compact_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      GaussianEulerUnitCompactTimeBounds.source (cut (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (var 7) (two*(two*compactDenominator (var 5) (var 6)))) :=
  closeUniv 8 (.impI (original_cut_source _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_relative_floor_cuts_increasing_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      (GaussianPartitionedFiniteSum.increasing cutF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ⋏
        ap2 cutF zero (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ≐ zero)) :=
  closeUniv 7 (.impI (.andI (original_increasing _ _ _ _ _ _ _ Prf.hyp0) (original_zero _ _ _ _ _ _ _)))


private theorem displacement_triangle (q u v N M U : PTm n)
    (h₁ : Γ ⊢[PRAAx] RationalValueBounds.radius q u one M)
    (h₂ : Γ ⊢[PRAAx] RationalValueBounds.radius u v (two*N) U) : Γ ⊢[PRAAx]
    RationalValueBounds.radius q v (two*N*M+U) (M*U) :=
  RationalValueBounds.radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (RationalValueBounds.radius_triangle q u v one M (two*N) U h₁ h₂)

theorem original_displacement (i k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source k N a C E T M)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (GaussianEuclideanDistanceName.fraction (cut i k N a C E T M) M)
      (reverseNode i (clock k E T) N a C E)
      (two*N*M+unit (clock k E T)) (M*unit (clock k E T)) := by
  have cs := original_cut_source i k N a C E T M hs
  have hM : Γ ⊢[PRAAx] le one M := le_trans cs.andE₁.andE₁ (le_of_lt cs.andE₁.andE₂)
  have quantized := RationalValueBounds.radius_symmetric _ _ one M
    (RationalNonnegativeFloor.quantization_error (node i k N a C E T) M
      (node_nonnegative i k N a C E T M hs) hM)
  have shifted := GaussianEulerUnitSubstitutionTiltedNodes.original_uniform_correction_error i (clock k E T) N a C E hi
  have actual : Γ ⊢[PRAAx] RationalValueBounds.radius (node i k N a C E T)
      (reverseNode i (clock k E T) N a C E) (two*N) (unit (clock k E T)) :=
    RationalValueBounds.radius_congr (node_below i k N a C E T hi).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) shifted
  exact displacement_triangle
    (GaussianEuclideanDistanceName.fraction (cut i k N a C E T M) M)
    (node i k N a C E T) (reverseNode i (clock k E T) N a C E) N M (unit (clock k E T)) quantized actual


theorem actual_original_floor_cut_displacement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⋏ le (var 0) (var 2)) ⟶
      RationalValueBounds.radius
        (GaussianEuclideanDistanceName.fraction (cut (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) (var 7))
        (reverseNode (var 0) (clock (var 1) (var 5) (var 6)) (var 2) (var 3) (var 4) (var 5))
        (two*var 2*var 7+unit (clock (var 1) (var 5) (var 6))) (var 7*unit (clock (var 1) (var 5) (var 6)))) :=
  closeUniv 8 (.impI (original_displacement _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionFloorCuts
