import IPRADerivations.Topology.DimensionObstruction
import IPRADerivations.Foundations.RationalFloors
import IPRADerivations.Core.LinearCombination

/-!
# The finite dimension obstruction for rational tables (`dimension_invariance_ipra`, `thm:finite`)

Packet: `topology/dimension_invariance_ipra`, `thm:finite`: "If `d > 0`, `N ≥ 1`, `h > 0`, and the
rational table `F` satisfies `eq:sep` and `eq:small`, then `d ≤ m`." `Topology/DimensionObstruction`
proves it for tables in natural units of `h/d`; here the table is rational and `h` is a positive
rational, both arbitrary primitive recursive terms, in every dimension `D = d' + 1` and for every
`m < D`.

Coding. Entry `j` of the table at the grid point `u` is `(P_j(u) − Q_j(u))/(R_j(u) + 1)` for terms
`P j`, `Q j`, `R j`; the unit is `h = (h₁ + 1)/(h₂ + 1)` with terms `h₁ = hn(b)`, `h₂ = hd(b)` of the
base `b = ⟨N, p⟩`. With the cross terms of `Foundations/RationalFloors`, `|F_j(u) − F_j(v)|` is
`|X − Y| / ((R_j(u)+1)(R_j(v)+1))`, so

* `rhSep g` (`eq:sep`, coordinate `g`): for `u` on the lower and `v` on the upper face, some `j` has
  `h₁' (R_u+1)(R_v+1) ≤ h₂' |X − Y|`, that is `|F_j(u) − F_j(v)| ≥ h`;
* `rhSmall` (`eq:small`, strict, as in the packet): at the vertices `u, v` of every Kuhn simplex and
  for every `j`, `D h₂' |X − Y| < h₁' (R_u+1)(R_v+1)`, that is `D |F_j(u) − F_j(v)| < h`.

The reduction to natural units is the table `G j` of `⌊D F_j/h⌋` translated by the common offset
`D h₂' S`, where `S(b) = Σ_{w ∈ G_D(N)} Σ_j Q_j(w)` (`offset`, a grid sum, so `Q_j(u) ≤ S` at every
grid point: `offset_ge`). `RationalFloors.rat_far` turns `rhSep` into `DimensionOccupancy.hSep` for
`G` (`sep_nat`) and `RationalFloors.rat_near` turns `rhSmall` into `DimensionObstruction.hSmall`
(`small_nat`); `DimensionObstruction.no_table` finishes (`rat_no_table`). `rat_obstruction` is the
closed sentence `∀ N p. ¬(eq:sep for every coordinate ∧ eq:small)`. No witness is extracted
(the witness of `thm:alternative` is `Topology/DimensionAlternative`).
-/

namespace LeanProofs.IPRA.Topology.DimensionRational

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm BigOperators
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Foundations.GridSums
open LeanProofs.IPRA.Foundations.GridSumsContext
open LeanProofs.IPRA.Foundations.GridSumsPoints
open LeanProofs.IPRA.Foundations.TermSums
open LeanProofs.IPRA.Foundations.BoundedCases
open LeanProofs.IPRA.Foundations.RationalFloors
open LeanProofs.IPRA.Topology.KuhnSimplices
open LeanProofs.IPRA.Topology.SpernerCube
open LeanProofs.IPRA.Topology.StaggeredCells (near dist)
open LeanProofs.IPRA.Topology.StaggeredGrids (fprod_one)
open LeanProofs.IPRA.Topology.DimensionOccupancy
open LeanProofs.IPRA.Topology.DimensionObstruction
open Equiv

set_option autoImplicit false

variable {n : ℕ}

/-! ## Small facts -/

/-- A term is at most a sum containing it. -/
theorem le_fsum {Γ : List (Fm PTm n)} {k : ℕ} (f : Fin k → PTm n) (i : Fin k) :
    Γ ⊢[PRAAx] le (f i) (fsum k f) := by
  refine le_of_eq_add (d := fsum k (fun i' => if i' = i then zero else f i')) (of_mk ?_)
  rw [Q.mk_add, mk_fsum, mk_fsum]
  have e : ∀ x, Q.mk Γ (f x) = (if x = i then Q.mk Γ (f x) else 0) + Q.mk Γ (if x = i then zero else f x) :=
    fun x => by split_ifs <;> simp [Q.mk_zero]
  rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- `sg x = 0` gives `x = 0`. -/
theorem eq_zero_of_sg {Γ : List (Fm PTm n)} {x : PTm n} (h : Γ ⊢[PRAAx] Signum.sg x ≐ zero) :
    Γ ⊢[PRAAx] x ≐ zero := by
  refine .orE (zero_or_succ x) Prf.hyp0 ?_
  have e : ((x ≐ succ (pred x)) :: Γ) ⊢[PRAAx] Signum.sg x ≐ succ zero :=
    (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans (Signum.sg_succ _)
  exact .botE _ (succ_ne_zero (a := zero) (e.eqSymm.eqTrans h.wk))

/-- `D ≤ z` gives `[z ≤ D − 1] = 0`, i.e. `1 ∸ (z ∸ d') = 0` for `D = d' + 1`. -/
theorem far_bit (d' : ℕ) {Γ : List (Fm PTm n)} {z : PTm n} (h : Γ ⊢[PRAAx] le (num (d' + 1)) z) :
    Γ ⊢[PRAAx] monus one (monus z (num d')) ≐ zero := by
  have e : Γ ⊢[PRAAx] z ≐ num d' + succ (monus z (num (d' + 1))) := by
    ipra_lc natEq (eq_add_of_le h)
  exact (congrMonus (.eqRefl _) ((congrMonus e (.eqRefl _)).eqTrans (add_monus' _ _))).eqTrans
    ((succ_monus_succ _ _).eqTrans (zero_monus _))

/-! ## The table and its offset -/

section Table

variable (d' m : ℕ) (P Q R : Fin m → PTm 1) (hn hd : PTm 1)

/-- The summand of the offset at a point of `[0, N]^D`, repacked over the stored base. -/
def offS : PTm 1 :=
  fsum m (fun j => col (Q j) (canon (d' + 1) (sndT (tl (d' + 1) (Syn.var 0))) (Syn.var 0)))

/-- The offset `S(b) = Σ_{w ∈ G_D(N)} Σ_j Q_j(w)`. -/
def offset (b : PTm n) : PTm n := Syn.subst ![pairT (succ (fstT b)) b] (gs 0 (d' + 1) (offS d' m Q))

@[simp] theorem subst_offset {k : ℕ} (σ : Fin n → PTm k) (b : PTm n) :
    Syn.subst σ (offset d' m Q b) = offset d' m Q (Syn.subst σ b) := by
  simp only [offset, Syn.subst_subst]; congr 1; funext i; fin_cases i; simp

/-- The natural value at `u` over the base `b`: `⌊D h₂' (P + (S h₁' R' ∸ Q)) / (h₁' R')⌋`. -/
def gval (j : Fin m) (u b : PTm n) : PTm n :=
  quo (numer (num (d' + 1)) (col hn b) (col hd b) (offset d' m Q b) (col (P j) u) (col (Q j) u) (col (R j) u))
    (denom (col hn b) (col (R j) u))

@[simp] theorem subst_gval {k : ℕ} (σ : Fin n → PTm k) (j : Fin m) (u b : PTm n) :
    Syn.subst σ (gval d' m P Q R hn hd j u b) = gval d' m P Q R hn hd j (Syn.subst σ u) (Syn.subst σ b) := by
  simp [gval, subst_ap2]

/-- The table in natural units of `h/D`: `G_j(x) = gval j x (tl x)`. -/
def G (j : Fin m) : PTm 1 := gval d' m P Q R hn hd j (Syn.var 0) (tl (d' + 1) (Syn.var 0))

theorem col_G (j : Fin m) (u : PTm n) :
    col (G d' m P Q R hn hd j) u = gval d' m P Q R hn hd j u (tl (d' + 1) u) := by
  simp [col, G]

theorem gval_base {Γ : List (Fm PTm n)} (j : Fin m) (u : PTm n) {b b' : PTm n} (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] gval d' m P Q R hn hd j u b ≐ gval d' m P Q R hn hd j u b' := by
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (gval d' m P Q R hn hd j (Syn.var 0 : PTm 2) (Syn.var 1))
    (σ := ![u, b]) (σ' := ![u, b']) (fun i => by fin_cases i; exacts [.eqRefl _, hb])
  simpa using e

theorem colG {Γ : List (Fm PTm n)} (j : Fin m) {b u : PTm n} (hu : GridPt (d' + 1) Γ b u) :
    Γ ⊢[PRAAx] col (G d' m P Q R hn hd j) u ≐ gval d' m P Q R hn hd j u b := by
  rw [col_G]; exact gval_base d' m P Q R hn hd j u hu.tl

/-- `Q_j(u) ≤ S(b)` at every grid point. -/
theorem offset_ge {Γ : List (Fm PTm n)} {b u : PTm n} (hu : GridPt (d' + 1) Γ b u) (j : Fin m) :
    Γ ⊢[PRAAx] le (col (Q j) u) (offset d' m Q b) := by
  let sb : PTm n := pairT (succ (fstT b)) b
  let is : Fin (d' + 1) → PTm n := fun r => proj (d' - r.val) u
  let y := pk (d' + 1) is sb
  have hproj : ∀ q, q < d' + 1 → (Γ ⊢[PRAAx] proj q y ≐ proj q u) := fun q hq => by
    refine (proj_pk (d' + 1) is _ q hq).eqTrans ?_
    simp only [is]; rw [show d' - (d' + 1 - 1 - q) = q by omega]; exact .eqRefl _
  have htl : Γ ⊢[PRAAx] tl (d' + 1) y ≐ sb := tl_pk _ _ _
  have hb : Γ ⊢[PRAAx] sndT (tl (d' + 1) y) ≐ b := (congrSnd htl).eqTrans (snd_pair _ _)
  have hcan : Γ ⊢[PRAAx] canon (d' + 1) (sndT (tl (d' + 1) y)) y ≐ u :=
    (canon_base (d' + 1) y hb).eqTrans ((canon_congr (d' + 1) b hproj).eqTrans hu.canon.eqSymm)
  have hS : Γ ⊢[PRAAx] Syn.subst ![y] (offS d' m Q) ≐ fsum m (fun j => col (Q j) u) := by
    simp only [offS, subst_fsum, subst_col, subst_canon, subst_tl, subst_sndT, Syn.subst_var,
      Matrix.cons_val_zero]
    exact fsum_congr (fun j => congrCol (Q j) hcan)
  have hbound : ∀ r, Γ ⊢[PRAAx] lt (is r) (fstT (tl 0 sb)) := fun r => by
    have hfst : Γ ⊢[PRAAx] fstT sb ≐ succ (fstT b) := fst_pair _ _
    refine lt_congr (.eqRefl _) hfst.eqSymm ?_
    exact (succ_monus_succ _ _).eqTrans (hu.le (d' - r.val) (by omega))
  have hge := gs_ge (offS d' m Q) (d' + 1) 0 Γ sb is hbound
  exact le_trans (le_fsum (fun j => col (Q j) u) j) (le_congr hS (.eqRefl _) hge)

end Table

/-! ## The rational hypotheses -/

section Hyps

variable (d' m : ℕ) (P Q R : Fin m → PTm 1) (hn hd : PTm 1)

/-- `h₁' (R_u+1)(R_v+1)`: the threshold `h` cleared of denominators. -/
def thr (j : Fin m) (u v b : PTm n) : PTm n :=
  succ (col hn b) * (succ (col (R j) u) * succ (col (R j) v))

/-- `|X − Y|` for entry `j` at `u, v`. -/
def gap (j : Fin m) (u v : PTm n) : PTm n :=
  dist (crossX (col (P j) u) (col (Q j) u) (col (R j) u) (col (P j) v) (col (Q j) v) (col (R j) v))
    (crossY (col (P j) u) (col (Q j) u) (col (R j) u) (col (P j) v) (col (Q j) v) (col (R j) v))

@[simp] theorem subst_thr {k : ℕ} (σ : Fin n → PTm k) (j : Fin m) (u v b : PTm n) :
    Syn.subst σ (thr m R hn j u v b) = thr m R hn j (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ b) := by
  simp [thr]

@[simp] theorem subst_gap {k : ℕ} (σ : Fin n → PTm k) (j : Fin m) (u v : PTm n) :
    Syn.subst σ (gap m P Q R j u v) = gap m P Q R j (Syn.subst σ u) (Syn.subst σ v) := by
  simp [gap]

/-- `eq:sep` for coordinate `g` at `u, v`: some entry has `thr ≤ h₂' · gap`. -/
def rsepBody (g : ℕ) (u v b : PTm n) : Fm PTm n :=
  gridImp (d' + 1) u b (gridImp (d' + 1) v b ((proj (d' - g) u ≐ zero) ⟶ ((proj (d' - g) v ≐ fstT b) ⟶
    (fprod m (fun j => Signum.sg (monus (thr m R hn j u v b) (succ (col hd b) * gap m P Q R j u v))) ≐ zero))))

/-- `eq:sep` for coordinate `g`. -/
def rhSep (g : ℕ) (b : PTm n) : Fm PTm n :=
  Fm.all (Fm.all (rsepBody d' m P Q R hn hd g (Syn.var 1) (Syn.var 0) (Syn.shift (Syn.shift b))))

@[simp] theorem subst_rsepBody {k : ℕ} (σ : Fin n → PTm k) (g : ℕ) (u v b : PTm n) :
    (rsepBody d' m P Q R hn hd g u v b).subst σ =
      rsepBody d' m P Q R hn hd g (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ b) := by
  simp [rsepBody]

@[simp] theorem subst_rhSep {k : ℕ} (σ : Fin n → PTm k) (g : ℕ) (b : PTm n) :
    (rhSep d' m P Q R hn hd g b).subst σ = rhSep d' m P Q R hn hd g (Syn.subst σ b) := by
  simp [rhSep, subst_up_shift', Syn.up]

theorem rsep_at {Γ : List (Fm PTm n)} {g : ℕ} {b : PTm n} (h : Γ ⊢[PRAAx] rhSep d' m P Q R hn hd g b)
    (u v : PTm n) : Γ ⊢[PRAAx] rsepBody d' m P Q R hn hd g u v b := by
  have a := Prf.allE u h
  simp only [Fm.subst_all, subst_rsepBody, Syn.subst_var] at a
  have a2 := Prf.allE v a
  simp only [subst_rsepBody] at a2
  simpa [Syn.up, Syn.subst_inst_shift, subst_up_shift'] using a2

/-- `eq:small` at the simplices of a base point `a`: `Σ_{π,s,t,j} ((D h₂' gap + 1) ∸ thr) = 0`. -/
noncomputable def rsmallSum (a b : PTm n) : PTm n :=
  ftsum (fun π : Perm (Fin (d' + 1)) => fsum (d' + 2) (fun s => fsum (d' + 2) (fun t => fsum m (fun j =>
    monus (succ (num (d' + 1) * succ (col hd b) *
        gap m P Q R j (vert (d' + 1) π s.val a) (vert (d' + 1) π t.val a)))
      (thr m R hn j (vert (d' + 1) π s.val a) (vert (d' + 1) π t.val a) b)))))

/-- `eq:small` at every base point. -/
noncomputable def rhSmall (b : PTm n) : Fm PTm n :=
  Fm.all ((Syn.var 0 ≐ canon (d' + 1) (Syn.shift b) (Syn.var 0)) ⟶
    ((bsumLt (d' + 1) (Syn.var 0) (Syn.shift b) ≐ zero) ⟶
      (rsmallSum d' m P Q R hn hd (Syn.var 0) (Syn.shift b) ≐ zero)))

@[simp] theorem subst_rsmallSum {k : ℕ} (σ : Fin n → PTm k) (a b : PTm n) :
    Syn.subst σ (rsmallSum d' m P Q R hn hd a b) = rsmallSum d' m P Q R hn hd (Syn.subst σ a) (Syn.subst σ b) := by
  simp [rsmallSum]

@[simp] theorem subst_rhSmall {k : ℕ} (σ : Fin n → PTm k) (b : PTm n) :
    (rhSmall d' m P Q R hn hd b).subst σ = rhSmall d' m P Q R hn hd (Syn.subst σ b) := by
  simp [rhSmall, subst_up_shift', Syn.up]

theorem rsmall_at {Γ : List (Fm PTm n)} {b a : PTm n} (h : Γ ⊢[PRAAx] rhSmall d' m P Q R hn hd b)
    (h₁ : Γ ⊢[PRAAx] a ≐ canon (d' + 1) b a) (h₂ : Γ ⊢[PRAAx] bsumLt (d' + 1) a b ≐ zero) :
    Γ ⊢[PRAAx] rsmallSum d' m P Q R hn hd a b ≐ zero := by
  have e := Prf.allE a h
  simp only [Fm.subst_imp, Fm.subst_eq, subst_canon, subst_bsumLt, subst_rsmallSum,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at e
  exact .impE (.impE e h₁) h₂

end Hyps

/-! ## From rational to natural units -/

section Reduction

variable (d' m : ℕ) (P Q R : Fin m → PTm 1) (hn hd : PTm 1)

/-- Separated entries give natural values at distance `≥ D`. -/
theorem far_entry {Γ : List (Fm PTm n)} {b u v : PTm n} (hu : GridPt (d' + 1) Γ b u)
    (hv : GridPt (d' + 1) Γ b v) (j : Fin m) :
    Γ ⊢[PRAAx] le (thr m R hn j u v b) (succ (col hd b) * gap m P Q R j u v) ⟶
      (monus one (monus (dist (col (G d' m P Q R hn hd j) u) (col (G d' m P Q R hn hd j) v)) (num d')) ≐ zero) := by
  refine .impI ?_
  let Δ : List (Fm PTm n) := le (thr m R hn j u v b) (succ (col hd b) * gap m P Q R j u v) :: Γ
  have hu' : GridPt (d' + 1) Δ b u := ⟨hu.canon.wk, hu.bound.wk⟩
  have hv' : GridPt (d' + 1) Δ b v := ⟨hv.canon.wk, hv.bound.wk⟩
  have h0 : Δ ⊢[PRAAx] le (thr m R hn j u v b) (succ (col hd b) * gap m P Q R j u v) := Prf.hyp0
  have r : Δ ⊢[PRAAx] le (num (d' + 1)) (dist (gval d' m P Q R hn hd j u b) (gval d' m P Q R hn hd j v b)) :=
    rat_far (offset_ge d' m Q hu' j) (offset_ge d' m Q hv' j) h0
  exact far_bit d' (le_congr (.eqRefl _) (congrDist (colG d' m P Q R hn hd j hu')
    (colG d' m P Q R hn hd j hv')).eqSymm r)

theorem sep_point {Γ : List (Fm PTm n)} {b u v : PTm n} (hu : GridPt (d' + 1) Γ b u)
    (hv : GridPt (d' + 1) Γ b v)
    (hr : Γ ⊢[PRAAx] fprod m (fun j => Signum.sg (monus (thr m R hn j u v b) (succ (col hd b) * gap m P Q R j u v))) ≐ zero) :
    Γ ⊢[PRAAx] fprod m (fun j => monus one (monus (dist (col (G d' m P Q R hn hd j) u)
      (col (G d' m P Q R hn hd j) v)) (num d'))) ≐ zero := by
  refine bounded_cases 1 (fun j : Fin m => Signum.sg (monus (thr m R hn j u v b) (succ (col hd b) * gap m P Q R j u v)))
    _ (fun j => le_one_monus _) (fun ρ hρ Δ' hext hκ => ?_)
  by_cases hall : ∀ j, ρ j = 1
  · refine .botE _ (succ_ne_zero (a := zero) ?_)
    refine (fprod_one (fun j => ?_)).eqSymm.eqTrans (hext _ hr)
    have hj := hκ j
    rw [hall j] at hj
    exact hj
  · simp only [not_forall] at hall
    obtain ⟨j, hj⟩ := hall
    have h0 : ρ j = 0 := by have := hρ j; omega
    have hj' := hκ j
    rw [h0] at hj'
    exact fprod_eq_zero j (Prf.impE (hext _ (far_entry d' m P Q R hn hd hu hv j)) (eq_zero_of_sg hj'))

/-- `eq:sep` for the rational table gives `DimensionOccupancy.hSep` for `G`. -/
theorem sep_body {Γ : List (Fm PTm n)} {g : ℕ} {b u v : PTm n}
    (hr : Γ ⊢[PRAAx] rsepBody d' m P Q R hn hd g u v b) :
    Γ ⊢[PRAAx] sepBody d' m (G d' m P Q R hn hd) g u v b := by
  refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
  let Δ : List (Fm PTm n) := (proj (d' - g) v ≐ fstT b) :: (proj (d' - g) u ≐ zero) ::
    (bsum (d' + 1) v b ≐ zero) :: (v ≐ canon (d' + 1) b v) :: (bsum (d' + 1) u b ≐ zero) ::
    (u ≐ canon (d' + 1) b u) :: Γ
  have hu : GridPt (d' + 1) Δ b u := ⟨.hyp (by simp [Δ]), .hyp (by simp [Δ])⟩
  have hv : GridPt (d' + 1) Δ b v := ⟨.hyp (by simp [Δ]), .hyp (by simp [Δ])⟩
  have hr' : Δ ⊢[PRAAx] rsepBody d' m P Q R hn hd g u v b := hr.wk.wk.wk.wk.wk.wk
  have h0 : Δ ⊢[PRAAx] proj (d' - g) u ≐ zero := Prf.hyp1
  have hN : Δ ⊢[PRAAx] proj (d' - g) v ≐ fstT b := Prf.hyp0
  have h6 := Prf.impE (Prf.impE (Prf.impE (Prf.impE (Prf.impE (Prf.impE hr' hu.canon) hu.bound) hv.canon)
    hv.bound) h0) hN
  exact sep_point d' m P Q R hn hd hu hv h6

theorem sep_nat {Γ : List (Fm PTm n)} {g : ℕ} {b : PTm n} (hs : Γ ⊢[PRAAx] rhSep d' m P Q R hn hd g b) :
    Γ ⊢[PRAAx] hSep d' m (G d' m P Q R hn hd) g b := by
  refine .allI (.allI ?_)
  have e := hs.shift.shift
  simp only [Fm.shift, subst_rhSep] at e
  exact sep_body d' m P Q R hn hd (rsep_at d' m P Q R hn hd e (Syn.var 1) (Syn.var 0))

/-- Small rational simplices give natural values within `1`. -/
theorem small_point {Γ : List (Fm PTm n)} {b a : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ canon (d' + 1) b a)
    (h₂ : Γ ⊢[PRAAx] bsumLt (d' + 1) a b ≐ zero) (hr : Γ ⊢[PRAAx] rsmallSum d' m P Q R hn hd a b ≐ zero) :
    Γ ⊢[PRAAx] smallSum d' m (G d' m P Q R hn hd) a ≐ zero := by
  have htl : Γ ⊢[PRAAx] tl (d' + 1) a ≐ b := (congrTl (d' + 1) h₁).eqTrans (tl_canon (d' + 1) b a)
  have hlt : ∀ q, q < d' + 1 → (Γ ⊢[PRAAx] lt (proj q a) (fstT b)) := fun q hq =>
    fsum_zero_elim (d' + 1) _ h₂ ⟨q, hq⟩
  have hgrid : ∀ (π : Perm (Fin (d' + 1))) (s : ℕ), GridPt (d' + 1) Γ b (vert (d' + 1) π s a) := fun π s => by
    obtain ⟨c₁, c₂⟩ := incr_grid (d' + 1) (vbit (d' + 1) π s) a b htl
      (fun q hq => le_of_lt (hlt q hq)) (fun q hq _ => hlt q hq)
    exact ⟨c₁, c₂⟩
  refine ftsum_zero (fun π => fsum_eq_zero (fun s => fsum_eq_zero (fun t => fsum_eq_zero (fun j => ?_))))
  have hz := fsum_zero_elim m _ (fsum_zero_elim (d' + 2) _ (fsum_zero_elim (d' + 2) _ (ftsum_zero_elim hr π) s) t) j
  have r := rat_near (S := offset d' m Q b) (offset_ge d' m Q (hgrid π s.val) j) (offset_ge d' m Q (hgrid π t.val) j) hz
  exact le_congr (congrDist (colG d' m P Q R hn hd j (hgrid π s.val)) (colG d' m P Q R hn hd j (hgrid π t.val))).eqSymm
    (.eqRefl _) r

theorem small_nat {Γ : List (Fm PTm n)} {b : PTm n} (hs : Γ ⊢[PRAAx] rhSmall d' m P Q R hn hd b) :
    Γ ⊢[PRAAx] hSmall d' m (G d' m P Q R hn hd) b := by
  refine .allI (.impI (.impI ?_))
  have e := hs.shift
  simp only [Fm.shift, subst_rhSmall] at e
  exact small_point d' m P Q R hn hd Prf.hyp1 Prf.hyp0 (rsmall_at d' m P Q R hn hd e.wk.wk Prf.hyp1 Prf.hyp0)

/-- `thm:finite` for rational tables: separation for every coordinate and small simplices are
contradictory when `m < D`. -/
theorem rat_no_table (hdm : m < d' + 1) {Γ : List (Fm PTm n)} {b : PTm n}
    (hs : ∀ g, g ≤ d' → (Γ ⊢[PRAAx] rhSep d' m P Q R hn hd g b)) (hsm : Γ ⊢[PRAAx] rhSmall d' m P Q R hn hd b) :
    Γ ⊢[PRAAx] Fm.bot :=
  no_table d' m (G d' m P Q R hn hd) hdm (fun g hg => sep_nat d' m P Q R hn hd (hs g hg))
    (small_nat d' m P Q R hn hd hsm)

end Reduction

/-! ## The closed sentence -/

section Closed

variable (d' m : ℕ) (P Q R : Fin m → PTm 1) (hn hd : PTm 1)

/-- The hypotheses at the base `⟨N, p⟩`. -/
noncomputable def ratHyps : List (Fm PTm 2) :=
  List.ofFn (fun g : Fin (d' + 1) => rhSep d' m P Q R hn hd g.val base2) ++ [rhSmall d' m P Q R hn hd base2]

/-- `∀ N p. ¬ (eq:sep ∧ eq:small)` for a rational table to `m < D` coordinates. -/
noncomputable def ratFormula : Fm PTm 2 := impAll (ratHyps d' m P Q R hn hd) Fm.bot

/-- `thm:finite` for every dimension `D = d' + 1`, every `m < D`, every rational table
`(P − Q)/(R + 1)` and every rational unit `h = (hn + 1)/(hd + 1)`, as a closed sentence of iPRA. -/
theorem rat_obstruction (hdm : m < d' + 1) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (ratFormula d' m P Q R hn hd) := by
  refine closeUniv 2 (impAll_intro _ _ _ (rat_no_table d' m P Q R hn hd hdm (b := base2)
    (fun g hg => .hyp ?_) (.hyp ?_)))
  · simp only [ratHyps, List.append_nil, List.mem_reverse, List.mem_append, List.mem_ofFn,
      List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl ⟨⟨g, by omega⟩, rfl⟩
  · simp [ratHyps]

end Closed

end LeanProofs.IPRA.Topology.DimensionRational
