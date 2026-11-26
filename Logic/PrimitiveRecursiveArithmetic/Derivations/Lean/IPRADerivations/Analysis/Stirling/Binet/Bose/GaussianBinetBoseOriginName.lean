import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseOriginExhaustion
import IPRADerivations.Analysis.Names.Order.GaussianFastValueCut

/-!
# The original Bose integral including the origin at a fixed horizon

Actual observations use the original positive compact integral with
a dyadic initial endpoint chosen from the requested accuracy.
-/

set_option autoImplicit false
set_option maxHeartbeats 540000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseOriginName

open_ipra
open GaussianBinetBoseCompact (evaluatorF gain)
open GaussianBinetBoseOriginExhaustion (cutData subst_cutData cut_regular ordered_rate width)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName
  (sampleData field0 field1 field2 field3 field4 field0_at field1_at field2_at field3_at field4_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent normalizer query_budget)
open GaussianNamedInverseRate (independentRate rate_at denominator_positive)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "CompactF" => GaussianBinetBoseCompact.nameF
local notation "panelDen" => GaussianBinetBoseOriginExhaustion.cutoff
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def source (X _Y D sign T : PTm n) : Fm PTm n :=
  GaussianRightHalfPlaneLogarithm.source X D sign ⋏ le one T

ipra_subst source [GaussianRightHalfPlaneLogarithm.source, GaussianRightHalfPlaneArgument.source]

def schedule (p D : PTm n) : PTm n := exponent D (succ p)

def data (X Y D sign T : PTm n) : PTm n := sampleData X Y D sign T zero

def sample (p X Y D sign T : PTm n) : PTm n :=
  ap2 CompactF (succ p) (cutData X Y D sign T (schedule p D))

def nameF : PR 2 := PTm.toPR
  (sample (var 0) (field0 (var 1)) (field1 (var 1)) (field2 (var 1)) (field3 (var 1)) (field4 (var 1)) : PTm 2)

ipra_subst schedule

ipra_subst data

ipra_subst sample

private theorem last_field {α : Type} (a b c d e f : α) : ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

theorem sample_at (p X Y D sign T : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data X Y D sign T) ≐ sample p X Y D sign T := by
  let x := data X Y D sign T
  have read : Γ ⊢[PRAAx] ap2 nameF p x ≐ sample p (field0 x) (field1 x) (field2 x) (field3 x) (field4 x) := by
    simpa only [nameF,ap2,subst_sample,GaussianCompactRiemannName.subst_field0,
      GaussianCompactRiemannName.subst_field1,GaussianCompactRiemannName.subst_field2,
      GaussianCompactRiemannName.subst_field3,GaussianCompactRiemannName.subst_field4,
      Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      toPR_eq (Γ := Γ) (sample (var 0) (field0 (var 1)) (field1 (var 1)) (field2 (var 1)) (field3 (var 1))
        (field4 (var 1)) : PTm 2) ![p,x]
  apply read.eqTrans
  simpa only [subst_sample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,last_field,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
    (σ := ![p,field0 x,field1 x,field2 x,field3 x,field4 x]) (σ' := ![p,X,Y,D,sign,T])
    (fun i => by fin_cases i; exact .eqRefl _; exact field0_at _ _ _ _ _ _; exact field1_at _ _ _ _ _ _;
                 exact field2_at _ _ _ _ _ _; exact field3_at _ _ _ _ _ _; exact field4_at _ _ _ _ _ _)

theorem schedule_positive (p D : PTm n) : Γ ⊢[PRAAx] le one (schedule p D) :=
  le_trans (zero_lt_succ p) (le_add_right (succ p) (normalizer D))

theorem schedule_monotone (p q D : PTm n) (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] le (schedule p D) (schedule q D) :=
  add_le_add_right (normalizer D)
    (le_congr (succ_eq_add_one p).eqSymm (succ_eq_add_one q).eqSymm (add_le_add_right one h))

private theorem cutoff_denominator_positive (X L : PTm n) (hX : Γ ⊢[PRAAx] le one X) :
    Γ ⊢[PRAAx] le one (panelDen L*(num 4*X)) :=
  positive_product _ _ (GaussianBinetBoseOriginExhaustion.cutoff_positive L)
    (positive_product _ _ (by ipra_le 3) hX)

private theorem unit_successor (p : PTm n) : Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p :=
  (pw_succ two p).eqTrans (mul_comm _ _)

theorem sample_canonical (p X Y D sign T : PTm n) :
    Γ ⊢[PRAAx] GaussianRationalHorner.canonical (ap2 nameF p (data X Y D sign T)) := by
  let L := schedule p D
  let E := panelDen L
  let C := width T L
  have hs : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (sample p X Y D sign T) :=
    GaussianCompactRiemannName.name_canonical evaluatorF (succ p) (E+one) C E (gain D E T) T
      (GaussianBinetArctangentQuadrature.fixedData X Y D sign)
  exact GaussianRationalHorner.canonical_congr (sample_at p X Y D sign T) hs

/-- Each actual observation of the fixed-horizon name agrees with a later
positive compact panel up to their independent dyadic allowances. -/
theorem late_observations (p q X Y D sign T L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign T) (hL : Γ ⊢[PRAAx] le (schedule p D) L) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign T)) (ap2 CompactF q (cutData X Y D sign T L))
      (unit p+unit q) (unit p*unit q) := by
  let C := schedule p D
  let N := panelDen C*(num 4*X)
  let U := unit p
  let V := unit q
  let W := unit (succ p)
  let a := cutData X Y D sign T C
  let b := cutData X Y D sign T L
  have hX := h.andE₁.andE₁.andE₁
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) q
  have hw := unit_positive (Γ := Γ) (succ p)
  have hN : Γ ⊢[PRAAx] le one N := cutoff_denominator_positive X C hX
  have hDen := denominator_positive N (succ p) q hN
  have hb : Γ ⊢[PRAAx] le (D*W) N := by
    have fourX : Γ ⊢[PRAAx] le one (num 4*X) := positive_product _ _ (by ipra_le 3) hX
    have cutoff_later : Γ ⊢[PRAAx] le (unit C) (panelDen C) :=
      GaussianExponentialReference.unit_monotone (le_succ_self C)
    exact le_trans (query_budget D (succ p))
      (le_trans cutoff_later (le_congr (by ipra_ring : Γ ⊢[PRAAx] panelDen C*one ≐ panelDen C) (.eqRefl N) (le_mul_mono (le_refl (panelDen C)) fourX)))
  have original := rate_at CompactF CompactF a b D N (succ p) q
    (ordered_rate X Y D sign T C L h.andE₁ h.andE₂ hL)
  have first : Γ ⊢[PRAAx] distanceBounded (sample p X Y D sign T) (ap2 CompactF q b)
      (two*V+W) (W*V) := by
    apply distance_radius_mono _ _ _ _ _ _ hDen (positive_product _ _ hw hv) ?_ original
    change Γ ⊢[PRAAx] le ((D*W*V+N*(W+V))*(W*V)) ((two*V+W)*(N*W*V))
    ipra_le 𝔞(W)*𝔞(V)*𝔞(V)*sl hb
  apply distance_congr (sample_at p X Y D sign T).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hw hv) (positive_product _ _ hu hv) ?_ first
  refine le_of_eq_add (d := zero) ?_
  have he := natEq (unit_successor (Γ := Γ) p)
  apply deriveNat
  dsimp only [U,V,W]
  ipra_simps
  rw [he]
  ring

private theorem relax_second (x y p q : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded x y (unit p+unit (succ q)) (unit p*unit (succ q))) :
    Γ ⊢[PRAAx] distanceBounded x y (unit p+unit q) (unit p*unit q) := by
  let U := unit p
  let V := unit q
  let W := unit (succ q)
  have grow : Γ ⊢[PRAAx] le V W := GaussianExponentialReference.unit_monotone (le_succ_self q)
  apply distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive p) (unit_positive (succ q)))
    (positive_product _ _ (unit_positive p) (unit_positive q)) ?_ h
  change Γ ⊢[PRAAx] le ((U+W)*(U*V)) ((U+V)*(U*W))
  ipra_le 𝔞(U)*𝔞(U)*sl grow

theorem observations (p q X Y D sign T : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign T) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign T)) (ap2 nameF q (data X Y D sign T))
      (unit p+unit q) (unit p*unit q) := by
  refine (le_total (schedule p D) (schedule q D)).orE ?_ ?_
  · exact relax_second _ _ p q
      (distance_congr (.eqRefl _) (sample_at q X Y D sign T).eqSymm (.eqRefl _) (.eqRefl _)
        (late_observations p (succ q) X Y D sign T (schedule q D) h.wk Prf.hyp0))
  · have raw := relax_second _ _ q p
      (distance_congr (.eqRefl _) (sample_at p X Y D sign T).eqSymm (.eqRefl _) (.eqRefl _)
        (late_observations q (succ p) X Y D sign T (schedule p D) h.wk Prf.hyp0))
    exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) raw)

theorem regular (X Y D sign T : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign T) :
    Γ ⊢[PRAAx] pointCN nameF (data X Y D sign T) := by
  refine .allI (.allI ?_)
  let s (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s T) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,subst_source] using h.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,Δ,s,Syn.shift,subst_data] using
    observations (var 1) (var 0) (s X) (s Y) (s D) (s sign) (s T) hs

private theorem prefix_diagonal (p X Y D sign T L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign T) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign T))
      (ap2 CompactF p (cutData X Y D sign T L))
      (diagonalNumerator D (panelDen L*(num 4*X)) two p) (diagonalDenominator (panelDen L*(num 4*X)) p) := by
  let C := schedule p D
  let U := unit p
  let W := unit (succ p)
  let N := panelDen L*(num 4*X)
  have hu := unit_positive (Γ := Γ) p
  have hN : Γ ⊢[PRAAx] le one N := cutoff_denominator_positive X L h.andE₁.andE₁.andE₁
  have hNU := positive_product _ _ hN hu
  refine (le_total L C).orE ?_ ?_
  · have raw := rate_at CompactF CompactF (cutData X Y D sign T L) (cutData X Y D sign T C) D N p (succ p)
      (ordered_rate X Y D sign T L C h.andE₁.wk h.andE₂.wk Prf.hyp0)
    have den := denominator_positive N p (succ p) hN
    apply distance_congr (sample_at p X Y D sign T).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    apply distance_radius_mono _ _ _ _ _ _ den.wk hNU.wk ?_ (distance_symmetric _ _ _ _ den.wk raw)
    have grow : le L C :: Γ ⊢[PRAAx] le U W := GaussianExponentialReference.unit_monotone (le_succ_self p)
    change (le L C :: Γ) ⊢[PRAAx] le ((D*U*W+N*(U+W))*(N*U)) ((D*U+two*N)*(N*U*W))
    ipra_le 𝔞(N)*𝔞(N)*𝔞(U)*sl grow
  · apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu.wk hu.wk) hNU.wk ?_
      (late_observations p p X Y D sign T L h.wk Prf.hyp0)
    refine le_of_eq_add (d := D*U*U*U) ?_
    dsimp only [diagonalNumerator,diagonalDenominator,U,N]
    ipra_ring

/-- The fixed-horizon name and any positive compact dyadic panel differ by
at most `D/(4 X 2^(L+1))` plus their independent observation allowances. -/
theorem prefix_rate (X Y D sign T L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign T) :
    Γ ⊢[PRAAx] independentRate nameF CompactF (data X Y D sign T) (cutData X Y D sign T L)
      D (panelDen L*(num 4*X)) := by
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ two
    (cutoff_denominator_positive X L h.andE₁.andE₁.andE₁)
    (regular X Y D sign T h) (cut_regular X Y D sign T L h.andE₁ h.andE₂)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s T) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,subst_source] using h.shift
  simpa only [diagonalEnvelope,Syn.shift,s,subst_data,subst_cutData,GaussianBinetBoseOriginExhaustion.subst_cutoff,
    GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul,PTm.subst_num,two,one,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using prefix_diagonal (var 0) (s X) (s Y) (s D) (s sign) (s T) (s L) hs

theorem actual_second_Binet_fixed_horizon_at_origin_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (regular _ _ _ _ _ Prf.hyp0))

theorem actual_second_Binet_fixed_horizon_dyadic_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ independentRate nameF CompactF
      (data (var 0) (var 1) (var 2) (var 3) (var 4))
      (cutData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (panelDen (var 5)*(num 4*var 0))) :=
  closeUniv 6 (.impI (prefix_rate _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseOriginName
