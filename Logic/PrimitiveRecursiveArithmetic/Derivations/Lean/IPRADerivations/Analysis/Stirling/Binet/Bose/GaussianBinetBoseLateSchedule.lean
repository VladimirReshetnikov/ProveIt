import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseImproperFrozen

/-!
# Independent clock and mesh choices for the improper Bose comparison

Choose the compact clock and its geometric count before choosing the
literal clock. The π clock then permits an external lower bound. Once
π is fixed, choose a multiple of the original compact mesh and the final
frozen clock. These last three choices can accommodate lower bounds
from a separate finite transform on the same frozen matrix.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseLateSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetBoseImproperFrozen (baseMesh refinementCost freezingCost alignmentCost)
open GaussianBinetBoseOriginExhaustion (cutoff width cutoff_positive width_positive)
open GaussianBinetBoseFrozenSuffix (fullMesh)
open GaussianBinetSecondDecayFrozenTail (mesh)
open GaussianBinetSecondDecaySharedTail (clockFloor)
open GaussianBinetSecondDecayPiBridge (budget)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (precision mesh_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def originClock (h D K I : PTm n) : PTm n := exponent (D+I*(two*K)) h

def compactClock (h D T L : PTm n) : PTm n := exponent (refinementCost D T L) h

def extraRows (s L : PTm n) : PTm n := cutoff L*cutoff L*unit s

def literalClock (h s K T L N : PTm n) : PTm n :=
  exponent (freezingCost K T L N) (precision s T+h)

def piClock (u N T minimum : PTm n) : PTm n := exponent (budget N T) (u+minimum)

def meshMultiplier (T N k minimum : PTm n) : PTm n := mesh T (succ N) k+minimum

def meshBase (s D T L N k minimum : PTm n) : PTm n := baseMesh s D T L*meshMultiplier T N k minimum

def meshRefinement (T L N k minimum : PTm n) : PTm n := width T L*meshMultiplier T N k minimum

def frozenClock (h u T L N k M minimum : PTm n) : PTm n :=
  exponent (alignmentCost T L N) (u+(minimum+(clockFloor M T (succ N) k+h)))

@[simp] theorem subst_originClock {m : ℕ} (σ : Fin n → PTm m) (h D K I : PTm n) :
    Syn.subst σ (originClock h D K I) = originClock (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ K) (Syn.subst σ I) := by
  simp [originClock,two]

@[simp] theorem subst_compactClock {m : ℕ} (σ : Fin n → PTm m) (h D T L : PTm n) :
    Syn.subst σ (compactClock h D T L) = compactClock (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ T) (Syn.subst σ L) := by
  simp [compactClock,refinementCost]

@[simp] theorem subst_extraRows {m : ℕ} (σ : Fin n → PTm m) (s L : PTm n) :
    Syn.subst σ (extraRows s L) = extraRows (Syn.subst σ s) (Syn.subst σ L) := by simp [extraRows]

@[simp] theorem subst_literalClock {m : ℕ} (σ : Fin n → PTm m) (h s K T L N : PTm n) :
    Syn.subst σ (literalClock h s K T L N) = literalClock (Syn.subst σ h) (Syn.subst σ s) (Syn.subst σ K)
      (Syn.subst σ T) (Syn.subst σ L) (Syn.subst σ N) := by simp [literalClock,freezingCost]

@[simp] theorem subst_piClock {m : ℕ} (σ : Fin n → PTm m) (u N T minimum : PTm n) :
    Syn.subst σ (piClock u N T minimum) = piClock (Syn.subst σ u) (Syn.subst σ N) (Syn.subst σ T) (Syn.subst σ minimum) := by
  simp [piClock]

@[simp] theorem subst_meshMultiplier {m : ℕ} (σ : Fin n → PTm m) (T N k minimum : PTm n) :
    Syn.subst σ (meshMultiplier T N k minimum) = meshMultiplier (Syn.subst σ T) (Syn.subst σ N)
      (Syn.subst σ k) (Syn.subst σ minimum) := by simp [meshMultiplier]

@[simp] theorem subst_meshBase {m : ℕ} (σ : Fin n → PTm m) (s D T L N k minimum : PTm n) :
    Syn.subst σ (meshBase s D T L N k minimum) = meshBase (Syn.subst σ s) (Syn.subst σ D) (Syn.subst σ T) (Syn.subst σ L)
      (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ minimum) := by simp [meshBase,baseMesh]

@[simp] theorem subst_meshRefinement {m : ℕ} (σ : Fin n → PTm m) (T L N k minimum : PTm n) :
    Syn.subst σ (meshRefinement T L N k minimum) = meshRefinement (Syn.subst σ T) (Syn.subst σ L)
      (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ minimum) := by simp [meshRefinement]

@[simp] theorem subst_frozenClock {m : ℕ} (σ : Fin n → PTm m) (h u T L N k M minimum : PTm n) :
    Syn.subst σ (frozenClock h u T L N k M minimum) = frozenClock (Syn.subst σ h) (Syn.subst σ u) (Syn.subst σ T)
      (Syn.subst σ L) (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ M) (Syn.subst σ minimum) := by
  simp [frozenClock,alignmentCost]

/-- An available dyadic lower cutoff when no common lower cutoff has been fixed. -/
theorem origin_bounds (h D K I X : PTm n) (hx : Γ ⊢[PRAAx] le one X) :
    let E := cutoff (originClock h D K I)
    Γ ⊢[PRAAx] le (D*unit h) (E*(num 4*X)) ⋏ le ((I*(two*K))*unit h) (E*E) := by
  let L := originClock h D K I
  let E := cutoff L
  let A := I*(two*K)
  have paid : Γ ⊢[PRAAx] le ((D+A)*unit h) E :=
    le_trans (query_budget (D+A) h) (unit_monotone (le_succ_self L))
  have low := le_trans (mul_le_mul_right (unit h) (le_add_right D A)) paid
  have restored := le_trans (mul_le_mul_right (unit h) (le_add_left A D)) paid
  have he := cutoff_positive (Γ := Γ) L
  have hx' := positive_product (num 4) X (by ipra_le 3) hx
  have first : Γ ⊢[PRAAx] le E (E*(num 4*X)) :=
    le_congr (one_mul E) (mul_comm _ _) (mul_le_mul_right E hx')
  have second : Γ ⊢[PRAAx] le E (E*E) := le_congr (one_mul E) (.eqRefl _) (mul_le_mul_right E he)
  exact .andI (le_trans low first) (le_trans restored second)

theorem compact_bounds (h D T L : PTm n) :
    let s := compactClock h D T L
    Γ ⊢[PRAAx] le h s ⋏ le (refinementCost D T L*unit h) (cutoff L*unit s) := by
  let s := compactClock h D T L
  have cost := query_budget (Γ := Γ) (refinementCost D T L) h
  have grow : Γ ⊢[PRAAx] le (unit s) (cutoff L*unit s) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (unit s) (cutoff_positive L))
  exact .andI (le_add_right _ _) (le_trans cost grow)

theorem live_rows (I s L : PTm n) : Γ ⊢[PRAAx] le (cutoff L*cutoff L*unit s) (I+extraRows s L) :=
  le_add_left _ _

theorem literal_bounds (h s K T L N : PTm n) :
    let u := literalClock h s K T L N
    Γ ⊢[PRAAx] le (precision s T) u ⋏ le (freezingCost K T L N*unit h) (cutoff L*unit u) := by
  let v := precision s T+h
  let u := literalClock h s K T L N
  let A := freezingCost K T L N
  have vup : Γ ⊢[PRAAx] le v u := le_add_right _ _
  have main : Γ ⊢[PRAAx] le (A*unit h) (A*unit v) :=
    le_mul_mono (le_refl A) (unit_monotone (le_add_left h (precision s T)))
  have scale : Γ ⊢[PRAAx] le (unit u) (cutoff L*unit u) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (unit u) (cutoff_positive L))
  exact .andI (le_trans (le_add_right _ _) vup) (le_trans main (le_trans (query_budget A v) scale))

theorem pi_bounds (u N T minimum : PTm n) :
    let k := piClock u N T minimum
    Γ ⊢[PRAAx] le minimum k ⋏ le (budget N T*unit u) (unit k) := by
  let v := u+minimum
  let A := budget N T
  have step : Γ ⊢[PRAAx] le (A*unit u) (A*unit v) :=
    le_mul_mono (le_refl A) (unit_monotone (le_add_right u minimum))
  exact .andI (le_trans (le_add_left minimum u) (le_add_right v _)) (le_trans step (query_budget A v))

/-- The actual full mesh is large enough for a separate time-grid requirement.
The same bound also holds for the count of the initial lower-strip cells. -/
theorem mesh_bounds (s D T L N k minimum : PTm n) (ht : Γ ⊢[PRAAx] le one T) :
    let B := meshBase s D T L N k minimum
    let R := meshRefinement T L N k minimum
    let M := fullMesh T (cutoff L) B
    Γ ⊢[PRAAx] (le one B ⋏ le one R) ⋏ ((width T L*B ≐ R*baseMesh s D T L) ⋏
      (le (mesh T (succ N) k) M ⋏ (le minimum M ⋏ le minimum B))) := by
  let A := baseMesh s D T L
  let V := meshMultiplier T N k minimum
  let B := meshBase s D T L N k minimum
  let R := meshRefinement T L N k minimum
  let M := fullMesh T (cutoff L) B
  have hA : Γ ⊢[PRAAx] le one A := mesh_positive s (GaussianBinetBoseCompact.gain D (cutoff L) T) T
  have hMesh : Γ ⊢[PRAAx] le one (mesh T (succ N) k) := zero_lt_succ _
  have hPlus : Γ ⊢[PRAAx] le (mesh T (succ N) k) V := le_add_right _ _
  have hv := le_trans hMesh hPlus
  have hB : Γ ⊢[PRAAx] le one B := positive_product _ _ hA hv
  have hR : Γ ⊢[PRAAx] le one R := positive_product _ _ (width_positive T L ht) hv
  have he := positive_product _ _ ht (cutoff_positive L)
  have lower : Γ ⊢[PRAAx] le V B := le_congr (one_mul V) (.eqRefl _) (mul_le_mul_right V hA)
  have padded : Γ ⊢[PRAAx] le B M := le_congr (one_mul B) (.eqRefl _) (mul_le_mul_right B he)
  have minB : Γ ⊢[PRAAx] le minimum B := le_trans (le_add_left minimum (mesh T (succ N) k)) lower
  have counts : Γ ⊢[PRAAx] width T L*B ≐ R*A := by dsimp only [B,R,meshBase,meshRefinement,A]; ipra_ring
  exact .andI (.andI hB hR) (.andI counts (.andI (le_trans hPlus (le_trans lower padded)) (.andI (le_trans minB padded) minB)))

theorem frozen_bounds (h u T L N k M minimum : PTm n) :
    let q := frozenClock h u T L N k M minimum
    Γ ⊢[PRAAx] (le u q ⋏ le minimum q) ⋏
      (le (clockFloor M T (succ N) k) (unit q) ⋏ le (alignmentCost T L N*unit h) (cutoff L*unit q)) := by
  let B := clockFloor M T (succ N) k
  let v := u+(minimum+(B+h))
  let q := frozenClock h u T L N k M minimum
  let A := alignmentCost T L N
  have retime : Γ ⊢[PRAAx] le v q := le_add_right _ _
  have uu : Γ ⊢[PRAAx] le u v := le_add_right _ _
  have rr : Γ ⊢[PRAAx] le (minimum+(B+h)) v := le_add_left _ _
  have mm : Γ ⊢[PRAAx] le minimum v := le_trans (le_add_right minimum (B+h)) rr
  have mid : Γ ⊢[PRAAx] le (B+h) v := le_trans (le_add_left (B+h) minimum) rr
  have left : Γ ⊢[PRAAx] le B q := le_trans (le_add_right B h) (le_trans mid retime)
  have dq : Γ ⊢[PRAAx] le q (unit q) := le_trans (le_succ_self q) (RationalClosure.succ_le_two_pow q)
  have hp : Γ ⊢[PRAAx] le h v := le_trans (le_add_left h B) mid
  have paid : Γ ⊢[PRAAx] le (A*unit h) (unit q) :=
    le_trans (le_mul_mono (le_refl A) (unit_monotone hp)) (query_budget A v)
  have scale : Γ ⊢[PRAAx] le (unit q) (cutoff L*unit q) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (unit q) (cutoff_positive L))
  exact .andI (.andI (le_trans uu retime) (le_trans mm retime)) (.andI (le_trans left dq) (le_trans paid scale))

/-- The early time horizon, lower cutoff, and retained geometric count
can be fixed by another construction. The remaining choices are explicit. -/
theorem observation (h p T I L kMinimum meshMinimum qMinimum K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianBinetBoseImproperName.source X Y D sign K)
    (ht : Γ ⊢[PRAAx] le one T) (hi : Γ ⊢[PRAAx] le one I) (hp : Γ ⊢[PRAAx] le h p)
    (far : Γ ⊢[PRAAx] le ((two*K)*unit h) T) (near : Γ ⊢[PRAAx] le (D*unit h) (cutoff L*(num 4*X)))
    (tail : Γ ⊢[PRAAx] le ((num 11*K)*unit h) I)
    (restored : Γ ⊢[PRAAx] le ((I*(two*K))*unit h) (cutoff L*cutoff L)) :
    let s := compactClock h D T L
    let N := I+extraRows s L
    let u := literalClock h s K T L N
    let k := piClock u N T kMinimum
    let B := meshBase s D T L N k meshMinimum
    let M := fullMesh T (cutoff L) B
    let q := frozenClock h u T L N k M qMinimum
    Γ ⊢[PRAAx] distanceBounded
      (ap2 GaussianBinetBoseImproperName.nameF p (GaussianBinetBoseImproperName.data X Y D sign K))
      (GaussianBinetBoseFrozenMatrix.value q k I M X Y D sign zero T one) (num 9) (unit h) := by
  let s := compactClock h D T L
  let r := extraRows s L
  let N := I+r
  let u := literalClock h s K T L N
  let k := piClock u N T kMinimum
  let B := meshBase s D T L N k meshMinimum
  let R := meshRefinement T L N k meshMinimum
  let M := fullMesh T (cutoff L) B
  let q := frozenClock h u T L N k M qMinimum
  have compact := compact_bounds (Γ := Γ) h D T L
  have literal := literal_bounds (Γ := Γ) h s K T L N
  have pi := pi_bounds (Γ := Γ) u N T kMinimum
  have grid := mesh_bounds s D T L N k meshMinimum ht
  have final := frozen_bounds (Γ := Γ) h u T L N k M qMinimum
  exact GaussianBinetBoseImproperFrozen.observation_error h p s u q k I r T L B R K X Y D sign hz ht
    grid.andE₁.andE₁ grid.andE₁.andE₂ hi grid.andE₂.andE₁ hp compact.andE₁ literal.andE₁ final.andE₁.andE₁
    (live_rows I s L) pi.andE₂ grid.andE₂.andE₂.andE₁ final.andE₂.andE₁ far near compact.andE₂ literal.andE₂
    final.andE₂.andE₂ tail restored


end LeanProofs.IPRA.Analysis.GaussianBinetBoseLateSchedule
