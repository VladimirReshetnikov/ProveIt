import IPRADerivations.Topology.DimensionRational
import IPRADerivations.Foundations.DigitCodes
import IPRADerivations.Foundations.LeastBoundedWitness

/-!
# The finite witness alternative (`dimension_invariance_ipra`, `thm:alternative`)

Packet: `topology/dimension_invariance_ipra`, `thm:alternative`: "For every valid rational table
`F : G_d(N) → ℚ^m` with `d > m`, `N ≥ 1` and `h > 0`, a primitive recursive procedure returns one of:
(i) an index `i` and points `u ∈ L_i`, `v ∈ U_i` such that `dist(F(u), F(v)) < h`; (ii) a Kuhn
simplex and two of its vertices `u, v` such that `dist(F(u), F(v)) ≥ h/d`. The returned data can be
checked using rational arithmetic alone." Here for every `D = d' + 1`, `m < D`, and the rational
tables and units of `Topology/DimensionRational`.

The procedure is a finite family of least-witness searches (`Core/Search`) over digit codes
(`Foundations/DigitCodes`):

* `searchI g` (alternative (i), coordinate `g`): codes `c < (N+1)^{2D}` of pairs `(u, v)` of grid
  points, `u` the low and `v` the high `D` base-`(N+1)` digits; the check `fBodyI` is the sum of
  `[u ∉ G]`, `[v ∉ G]`, `[u_g ≠ 0]`, `|v_g − N|` and the number of entries `j` that are *not*
  `h`-close (`h₁'(R_u+1)(R_v+1) ≤ h₂' |X − Y|`), so it is `0` exactly for a witness of (i);
* `searchII (π, s, t, j)` (alternative (ii)): codes `c < N^D` of base points `a ∈ [0, N)^D`; the
  check `fBodyII` is `0` exactly when `D h₂' |X − Y| ≥ h₁'(R+1)(R'+1)` at the vertices `s, t` of the
  simplex `(a, π)` and entry `j`, that is `D |F_j(v_s) − F_j(v_t)| ≥ h`.

`alternative`: the closed sentence "for all `N`, `p`, some search of the family returns its least
witness `μ` below its bound and `check(μ) = 0`", a finite disjunction (`bigOr`) over
`Fin D ⊕ (Perm × Fin (D+1) × Fin (D+1) × Fin m)`. Proof (`alt_core`): each search either succeeds or
returns its bound (`search_cases`); if all return their bounds, every code fails (`search_minimal`),
so every grid pair on opposite faces has a separated entry (`rhSep`) and every simplex is small
(`rhSmall`), which `DimensionRational.rat_no_table` refutes (`bigOr_intro`).
-/

namespace LeanProofs.IPRA.Topology.DimensionAlternative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm BigOperators
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Search (mu search_minimal)
open LeanProofs.IPRA.Foundations.LeastBoundedWitness (mu_le accepted_of_lt)
open LeanProofs.IPRA.Foundations.GridSums
open LeanProofs.IPRA.Foundations.TermSums
open LeanProofs.IPRA.Foundations.BoundedCases (Extends)
open LeanProofs.IPRA.Topology.StaggeredGrids (bit_product_zero)
open LeanProofs.IPRA.Foundations.DigitCodes
open LeanProofs.IPRA.Topology.KuhnSimplices
open LeanProofs.IPRA.Topology.SpernerCube
open LeanProofs.IPRA.Topology.StaggeredCells (near dist)
open LeanProofs.IPRA.Topology.DimensionOccupancy
open LeanProofs.IPRA.Topology.DimensionObstruction
open LeanProofs.IPRA.Topology.DimensionRational
open Equiv

set_option autoImplicit false

variable {n : ℕ}

/-! ## Finite disjunctions -/

/-- `W 0 ∨ ⋯ ∨ W (k−1)`. -/
def bigOr : (k : ℕ) → (Fin k → Fm PTm n) → Fm PTm n
  | 0, _ => Fm.bot
  | k + 1, W => W 0 ⋎ bigOr k (fun i => W i.succ)

/-- If every `W i` is decided against an alternative `A i`, and all the alternatives together are
contradictory, then some `W i` holds. -/
theorem bigOr_intro {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (W A : Fin k → Fm PTm n), (∀ i, Γ ⊢[PRAAx] W i ⋎ A i) →
      (∀ Δ : List (Fm PTm n), Extends Γ Δ → (∀ i, Δ ⊢[PRAAx] A i) → (Δ ⊢[PRAAx] Fm.bot)) →
      (Γ ⊢[PRAAx] bigOr k W)
  | 0, _, _, _, hb => hb Γ (fun _ h => h) (fun i => i.elim0)
  | k + 1, W, A, hd, hb => by
    refine .orE (hd 0) (.orI₁ Prf.hyp0) (.orI₂ ?_)
    refine bigOr_intro k (fun i => W i.succ) (fun i => A i.succ) (fun i => (hd i.succ).wk)
      (fun Δ hext hA => hb Δ (fun ψ h => hext ψ h.wk) (fun i => ?_))
    refine Fin.cases ?_ (fun i => hA i) i
    exact hext _ Prf.hyp0

/-- A search either returns a checked witness below its bound or returns the bound. -/
theorem search_cases {Γ : List (Fm PTm n)} (f : PTm 2) (B x : PTm n) :
    Γ ⊢[PRAAx] (lt (mu f B x) B ⋏ (inst2 f (mu f B x) x ≐ zero)) ⋎ (mu f B x ≐ B) := by
  refine .orE (lt_or_le (mu f B x) B) (.orI₁ (.andI Prf.hyp0 (accepted_of_lt Prf.hyp0))) ?_
  exact .orI₂ (le_antisymm (mu_le _ _) Prf.hyp0)

/-! ## The searches -/

section Searches

variable (d' m : ℕ) (P Q R : Fin m → PTm 1) (hn hd : PTm 1)

/-- `[the entry j of (u, v) is h-close] = sg(thr ∸ h₂' gap)`. -/
def closeBit (j : Fin m) (u v b : PTm n) : PTm n :=
  Signum.sg (monus (thr m R hn j u v b) (succ (col hd b) * gap m P Q R j u v))

/-- The check of alternative (i) for the coordinate `g`. -/
def fBodyI (g : ℕ) (u v b : PTm n) : PTm n :=
  bsum (d' + 1) u b + bsum (d' + 1) v b + Signum.sg (proj (d' - g) u) + dist (proj (d' - g) v) (fstT b) +
    fsum m (fun j => monus one (closeBit m P Q R hn hd j u v b))

/-- The check of alternative (ii) for the simplex `π`, the vertices `s, t` and the entry `j`. -/
def fBodyII (π : Perm (Fin (d' + 1))) (s t : Fin (d' + 2)) (j : Fin m) (a b : PTm n) : PTm n :=
  Signum.sg (monus (thr m R hn j (vert (d' + 1) π s.val a) (vert (d' + 1) π t.val a) b)
    (num (d' + 1) * succ (col hd b) * gap m P Q R j (vert (d' + 1) π s.val a) (vert (d' + 1) π t.val a)))

/-- The digit base `N + 1` of alternative (i). -/
def P1 (b : PTm n) : PTm n := succ (fstT b)

/-- The bound `(N+1)^{2D}` of alternative (i). -/
def BI (b : PTm n) : PTm n := pwr (d' + 1) (P1 b) * pwr (d' + 1) (P1 b)

/-- The bound `N^D` of alternative (ii). -/
def BII (b : PTm n) : PTm n := pwr (d' + 1) (fstT b)

/-- The search for alternative (i), coordinate `g`: variable `0` is the code, `1` the base. -/
def searchI (g : ℕ) : PTm 2 :=
  fBodyI d' m P Q R hn hd g (dec (d' + 1) (P1 (Syn.var 1)) (Syn.var 0) (Syn.var 1))
    (dec (d' + 1) (P1 (Syn.var 1)) (quoK (d' + 1) (P1 (Syn.var 1)) (Syn.var 0)) (Syn.var 1)) (Syn.var 1)

/-- The search for alternative (ii). -/
def searchII (κ : Perm (Fin (d' + 1)) × Fin (d' + 2) × Fin (d' + 2) × Fin m) : PTm 2 :=
  fBodyII d' m P Q R hn hd κ.1 κ.2.1 κ.2.2.1 κ.2.2.2 (dec (d' + 1) (fstT (Syn.var 1)) (Syn.var 0) (Syn.var 1))
    (Syn.var 1)

@[simp] theorem subst_closeBit {k : ℕ} (σ : Fin n → PTm k) (j : Fin m) (u v b : PTm n) :
    Syn.subst σ (closeBit m P Q R hn hd j u v b) =
      closeBit m P Q R hn hd j (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ b) := by
  simp [closeBit]

@[simp] theorem subst_fBodyI {k : ℕ} (σ : Fin n → PTm k) (g : ℕ) (u v b : PTm n) :
    Syn.subst σ (fBodyI d' m P Q R hn hd g u v b) =
      fBodyI d' m P Q R hn hd g (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ b) := by
  simp [fBodyI]

@[simp] theorem subst_fBodyII {k : ℕ} (σ : Fin n → PTm k) (π : Perm (Fin (d' + 1))) (s t : Fin (d' + 2))
    (j : Fin m) (a b : PTm n) :
    Syn.subst σ (fBodyII d' m P Q R hn hd π s t j a b) =
      fBodyII d' m P Q R hn hd π s t j (Syn.subst σ a) (Syn.subst σ b) := by
  simp [fBodyII]

ipra_subst P1

@[simp] theorem subst_BI {k : ℕ} (σ : Fin n → PTm k) (b : PTm n) :
    Syn.subst σ (BI d' b) = BI d' (Syn.subst σ b) := by simp [BI]

@[simp] theorem subst_BII {k : ℕ} (σ : Fin n → PTm k) (b : PTm n) :
    Syn.subst σ (BII d' b) = BII d' (Syn.subst σ b) := by simp [BII]

theorem inst_searchI (g : ℕ) (c b : PTm n) :
    inst2 (searchI d' m P Q R hn hd g) c b =
      fBodyI d' m P Q R hn hd g (dec (d' + 1) (P1 b) c b) (dec (d' + 1) (P1 b) (quoK (d' + 1) (P1 b) c) b) b := by
  simp [inst2, searchI]

theorem inst_searchII (κ : Perm (Fin (d' + 1)) × Fin (d' + 2) × Fin (d' + 2) × Fin m) (c b : PTm n) :
    inst2 (searchII d' m P Q R hn hd κ) c b =
      fBodyII d' m P Q R hn hd κ.1 κ.2.1 κ.2.2.1 κ.2.2.2 (dec (d' + 1) (fstT b) c b) b := by
  simp [inst2, searchII]

theorem fBodyI_congr {Γ : List (Fm PTm n)} (g : ℕ) {u u' v v' : PTm n} (b : PTm n) (hu : Γ ⊢[PRAAx] u ≐ u')
    (hv : Γ ⊢[PRAAx] v ≐ v') : Γ ⊢[PRAAx] fBodyI d' m P Q R hn hd g u v b ≐ fBodyI d' m P Q R hn hd g u' v' b := by
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (fBodyI d' m P Q R hn hd g (Syn.var 0 : PTm 3) (Syn.var 1) (Syn.var 2))
    (σ := ![u, v, b]) (σ' := ![u', v', b]) (fun i => by fin_cases i; exacts [hu, hv, .eqRefl _])
  simpa using e

theorem fBodyII_congr {Γ : List (Fm PTm n)} (π : Perm (Fin (d' + 1))) (s t : Fin (d' + 2)) (j : Fin m)
    {a a' : PTm n} (b : PTm n) (ha : Γ ⊢[PRAAx] a ≐ a') :
    Γ ⊢[PRAAx] fBodyII d' m P Q R hn hd π s t j a b ≐ fBodyII d' m P Q R hn hd π s t j a' b := by
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (fBodyII d' m P Q R hn hd π s t j (Syn.var 0 : PTm 2) (Syn.var 1))
    (σ := ![a, b]) (σ' := ![a', b]) (fun i => by fin_cases i; exacts [ha, .eqRefl _])
  simpa using e

end Searches

/-! ## Failing searches give the hypotheses of `thm:finite` -/

section Failure

variable (d' m : ℕ) (P Q R : Fin m → PTm 1) (hn hd : PTm 1)

theorem dec_code {Γ : List (Fm PTm n)} {Pb cP u w b : PTm n} (hP : Γ ⊢[PRAAx] Pb ≐ succ cP)
    (hu : Γ ⊢[PRAAx] u ≐ canon (d' + 1) b u) (hlt : ∀ q, q < d' + 1 → (Γ ⊢[PRAAx] lt (proj q u) Pb)) :
    Γ ⊢[PRAAx] dec (d' + 1) Pb (enc (d' + 1) Pb u + pwr (d' + 1) Pb * w) b ≐ u :=
  (dec_enc hP (d' + 1) u w b hlt).eqTrans hu.eqSymm

theorem enc_zero (k : ℕ) {Γ : List (Fm PTm n)} (Pb x : PTm n) :
    Γ ⊢[PRAAx] enc k Pb x ≐ enc k Pb x + pwr k Pb * zero := by
  ipra_ring

/-- A failing search (i) for coordinate `g`: every opposite-face pair has a separated entry. -/
theorem sep_point_search {Γ : List (Fm PTm n)} {g : ℕ} {b u v : PTm n}
    (hμ : Γ ⊢[PRAAx] mu (searchI d' m P Q R hn hd g) (BI d' b) b ≐ BI d' b)
    (hu : GridPt (d' + 1) Γ b u) (hv : GridPt (d' + 1) Γ b v)
    (h0 : Γ ⊢[PRAAx] proj (d' - g) u ≐ zero) (hN : Γ ⊢[PRAAx] proj (d' - g) v ≐ fstT b) :
    Γ ⊢[PRAAx] fprod m (fun j => closeBit m P Q R hn hd j u v b) ≐ zero := by
  have hlt : ∀ (w : PTm n), GridPt (d' + 1) Γ b w → ∀ q, q < d' + 1 → (Γ ⊢[PRAAx] lt (proj q w) (P1 b)) :=
    fun w hw q hq => (succ_monus_succ _ _).eqTrans (hw.le q hq)
  let c : PTm n := enc (d' + 1) (P1 b) u + pwr (d' + 1) (P1 b) * enc (d' + 1) (P1 b) v
  have hc : Γ ⊢[PRAAx] lt c (BI d' b) := pair_lt (enc_lt _ _ (hlt u hu)) (enc_lt _ _ (hlt v hv))
  have hfail := search_minimal (lt_congr (.eqRefl _) hμ.eqSymm hc)
  rw [inst_searchI] at hfail
  have hP : Γ ⊢[PRAAx] P1 b ≐ succ (fstT b) := .eqRefl _
  have du : Γ ⊢[PRAAx] dec (d' + 1) (P1 b) c b ≐ u := dec_code d' hP hu.canon (hlt u hu)
  have dv : Γ ⊢[PRAAx] dec (d' + 1) (P1 b) (quoK (d' + 1) (P1 b) c) b ≐ v :=
    (congrDec (d' + 1) _ b (quoK_enc hP (d' + 1) u _ (hlt u hu))).eqTrans
      ((congrDec (d' + 1) _ b (enc_zero (d' + 1) _ v)).eqTrans (dec_code d' hP hv.canon (hlt v hv)))
  have hsum : Γ ⊢[PRAAx] fBodyI d' m P Q R hn hd g u v b ≐ fsum m (fun j => monus one (closeBit m P Q R hn hd j u v b)) := by
    refine (congrAdd (congrAdd (congrAdd (congrAdd hu.bound hv.bound)
      ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h0)).eqTrans Signum.sg_zero))
      ((congrAdd (congrMonus hN (.eqRefl _)) (congrMonus (.eqRefl _) hN)).eqTrans
        ((congrAdd (monus_self _) (monus_self _)).eqTrans (add_zero _)))) (.eqRefl _)).eqTrans ?_
    ipra_ring
  have hne : Γ ⊢[PRAAx] neg (fsum m (fun j => monus one (closeBit m P Q R hn hd j u v b)) ≐ zero) := by
    refine .impI (.impE hfail.wk ?_)
    exact ((fBodyI_congr d' m P Q R hn hd g b du dv).eqTrans hsum).wk.eqTrans Prf.hyp0
  refine bit_product_zero (fun j : Fin m => closeBit m P Q R hn hd j u v b) (fun _ => le_one_monus _) ?_
  intro Δ' hext hOne
  exact .impE (hext _ hne) (fsum_eq_zero (fun j =>
    (congrMonus (.eqRefl _) (hOne j)).eqTrans (monus_self _)))

theorem shift_mu (f : PTm 2) (B x : PTm n) : Syn.shift (mu f B x) = mu f (Syn.shift B) (Syn.shift x) := by
  simp [Syn.shift]

theorem sep_of_search {Γ : List (Fm PTm n)} {g : ℕ} {b : PTm n}
    (hμ : Γ ⊢[PRAAx] mu (searchI d' m P Q R hn hd g) (BI d' b) b ≐ BI d' b) :
    Γ ⊢[PRAAx] rhSep d' m P Q R hn hd g b := by
  refine .allI (.allI (.impI (.impI (.impI (.impI (.impI (.impI ?_)))))))
  have e := hμ.shift.shift
  simp only [Fm.shift, Fm.subst_eq, subst_BI, subst_ap2] at e
  let B := Syn.shift (Syn.shift b)
  let u : PTm (n + 2) := Syn.var 1
  let v : PTm (n + 2) := Syn.var 0
  let Δ : List (Fm PTm (n + 2)) := (proj (d' - g) v ≐ fstT B) :: (proj (d' - g) u ≐ zero) ::
    (bsum (d' + 1) v B ≐ zero) :: (v ≐ canon (d' + 1) B v) :: (bsum (d' + 1) u B ≐ zero) ::
    (u ≐ canon (d' + 1) B u) :: (Γ.map Fm.shift).map Fm.shift
  have hu : GridPt (d' + 1) Δ B u := ⟨.hyp (by simp [Δ]), .hyp (by simp [Δ])⟩
  have hv : GridPt (d' + 1) Δ B v := ⟨.hyp (by simp [Δ]), .hyp (by simp [Δ])⟩
  have h0 : Δ ⊢[PRAAx] proj (d' - g) u ≐ zero := Prf.hyp1
  have hN : Δ ⊢[PRAAx] proj (d' - g) v ≐ fstT B := Prf.hyp0
  have e' : Δ ⊢[PRAAx] mu (searchI d' m P Q R hn hd g) (BI d' B) B ≐ BI d' B := e.wk.wk.wk.wk.wk.wk
  exact sep_point_search d' m P Q R hn hd e' hu hv h0 hN

/-- Failing searches (ii): every simplex at a base point is small. -/
theorem small_point_search {Γ : List (Fm PTm n)} {b a : PTm n}
    (hμ : ∀ κ, Γ ⊢[PRAAx] mu (searchII d' m P Q R hn hd κ) (BII d' b) b ≐ BII d' b)
    (h₁ : Γ ⊢[PRAAx] a ≐ canon (d' + 1) b a) (h₂ : Γ ⊢[PRAAx] bsumLt (d' + 1) a b ≐ zero) :
    Γ ⊢[PRAAx] rsmallSum d' m P Q R hn hd a b ≐ zero := by
  have hlt : ∀ q, q < d' + 1 → (Γ ⊢[PRAAx] lt (proj q a) (fstT b)) := fun q hq =>
    fsum_zero_elim (d' + 1) _ h₂ ⟨q, hq⟩
  have hP : Γ ⊢[PRAAx] fstT b ≐ succ (proj 0 a + monus (fstT b) (succ (proj 0 a))) := by
    ipra_lc natEq (eq_add_of_le (hlt 0 (by omega)))
  let c : PTm n := enc (d' + 1) (fstT b) a
  have hc : Γ ⊢[PRAAx] lt c (BII d' b) := enc_lt _ _ hlt
  have da : Γ ⊢[PRAAx] dec (d' + 1) (fstT b) c b ≐ a :=
    (congrDec (d' + 1) _ b (enc_zero (d' + 1) _ a)).eqTrans (dec_code d' hP h₁ hlt)
  refine ftsum_zero (fun π => fsum_eq_zero (fun s => fsum_eq_zero (fun t => fsum_eq_zero (fun j => ?_))))
  have hfail := search_minimal (lt_congr (.eqRefl _) (hμ (π, s, t, j)).eqSymm hc)
  rw [inst_searchII] at hfail
  have hb := fBodyII_congr d' m P Q R hn hd π s t j b da
  refine .orE (lt_or_le (num (d' + 1) * succ (col hd b) *
      gap m P Q R j (vert (d' + 1) π s.val a) (vert (d' + 1) π t.val a))
    (thr m R hn j (vert (d' + 1) π s.val a) (vert (d' + 1) π t.val a) b)) Prf.hyp0 ?_
  refine .botE _ (.impE hfail.wk ?_)
  exact hb.wk.eqTrans ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans Signum.sg_zero)

theorem small_of_search {Γ : List (Fm PTm n)} {b : PTm n}
    (hμ : ∀ κ, Γ ⊢[PRAAx] mu (searchII d' m P Q R hn hd κ) (BII d' b) b ≐ BII d' b) :
    Γ ⊢[PRAAx] rhSmall d' m P Q R hn hd b := by
  refine .allI (.impI (.impI ?_))
  have e : ∀ κ, (Γ.map Fm.shift) ⊢[PRAAx] mu (searchII d' m P Q R hn hd κ) (BII d' (Syn.shift b)) (Syn.shift b) ≐
      BII d' (Syn.shift b) := fun κ => by
    have e := (hμ κ).shift
    simp only [Fm.shift, Fm.subst_eq, subst_BII, subst_ap2] at e
    exact e
  exact small_point_search d' m P Q R hn hd (fun κ => (e κ).wk.wk) Prf.hyp1 Prf.hyp0

end Failure

/-! ## The alternative -/

section Alternative

variable (d' m : ℕ) (P Q R : Fin m → PTm 1) (hn hd : PTm 1)

/-- The index set of the searches. -/
abbrev Idx (d' m : ℕ) : Type := Fin (d' + 1) ⊕ (Perm (Fin (d' + 1)) × Fin (d' + 2) × Fin (d' + 2) × Fin m)

/-- The search with index `i`, its bound and its success formula at the base `b`. -/
def wit (b : PTm n) : Idx d' m → Fm PTm n
  | Sum.inl g => lt (mu (searchI d' m P Q R hn hd g.val) (BI d' b) b) (BI d' b) ⋏
      (inst2 (searchI d' m P Q R hn hd g.val) (mu (searchI d' m P Q R hn hd g.val) (BI d' b) b) b ≐ zero)
  | Sum.inr κ => lt (mu (searchII d' m P Q R hn hd κ) (BII d' b) b) (BII d' b) ⋏
      (inst2 (searchII d' m P Q R hn hd κ) (mu (searchII d' m P Q R hn hd κ) (BII d' b) b) b ≐ zero)

/-- The failure formula of the search with index `i`. -/
def fail (b : PTm n) : Idx d' m → Fm PTm n
  | Sum.inl g => mu (searchI d' m P Q R hn hd g.val) (BI d' b) b ≐ BI d' b
  | Sum.inr κ => mu (searchII d' m P Q R hn hd κ) (BII d' b) b ≐ BII d' b

/-- `thm:alternative` at the base `b`: some search of the family succeeds. -/
noncomputable def altAt (b : PTm n) : Fm PTm n :=
  bigOr (Fintype.card (Idx d' m)) (fun i => wit d' m P Q R hn hd b ((Fintype.equivFin (Idx d' m)).symm i))

theorem alt_core (hdm : m < d' + 1) {Γ : List (Fm PTm n)} (b : PTm n) :
    Γ ⊢[PRAAx] altAt d' m P Q R hn hd b := by
  let e := Fintype.equivFin (Idx d' m)
  refine bigOr_intro _ _ (fun i => fail d' m P Q R hn hd b (e.symm i)) (fun i => ?_) (fun Δ _ hA => ?_)
  · cases h : e.symm i with
    | inl g => exact search_cases _ _ _
    | inr κ => exact search_cases _ _ _
  · have hA' : ∀ x : Idx d' m, Δ ⊢[PRAAx] fail d' m P Q R hn hd b x := fun x => by
      have := hA (e x); simpa using this
    refine rat_no_table d' m P Q R hn hd hdm (b := b) (fun g hg => ?_) ?_
    · exact sep_of_search d' m P Q R hn hd (hA' (Sum.inl ⟨g, by omega⟩))
    · exact small_of_search d' m P Q R hn hd (fun κ => hA' (Sum.inr κ))

/-- `thm:alternative` for every dimension `D = d' + 1`, every `m < D`, every rational table and every
rational unit, as a closed sentence of iPRA: for all `N`, `p` one of the searches returns a witness
below its bound that passes its check. -/
theorem alternative (hdm : m < d' + 1) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (altAt d' m P Q R hn hd base2) :=
  closeUniv 2 (alt_core d' m P Q R hn hd hdm base2)

end Alternative

end LeanProofs.IPRA.Topology.DimensionAlternative
