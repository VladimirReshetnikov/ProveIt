import IPRADerivations.Topology.SpernerCube
import IPRADerivations.Topology.StaggeredGrids
import IPRADerivations.Topology.LeadingBits
import IPRADerivations.Foundations.BoundedCases
import IPRADerivations.Foundations.GridSumsPoints

/-!
# The occupancy colouring of the dimension obstruction in every dimension (`dimension_invariance_ipra`)

Packet: `topology/dimension_invariance_ipra`, Section "Coloring from the lower faces", for every
dimension `D = d' + 1` and every number `m` of target coordinates. The table is `m` terms `F j` in
the packed point (natural values in units of `h/D`, as in `Topology/DimensionTwo`), on the grid
`G_D(N)` over the base `b = ⟨N, p⟩` of `Topology/SpernerCube`; grid `g < D` belongs to coordinate
`g`, the entry `D − 1 − g` of the packed point.

* `occ g v`: the number of points `w` of the lower face of coordinate `g` whose cell vector in grid
  `g` equals that of `v` (the packet's finite scan `Cell_g(F(v)) ∈ S_g`), a closed grid sum over
  `[0, N]^D` whose base stores `N + 1`, the cells of `v` and `b`; `bit g v = 1 ∸ sg(occ g v)`;
* `lamT`: the colour `eq:color`, the number of leading unoccupied grids (`Topology/LeadingBits`);
* `occ_pos`: on the lower face of coordinate `g`, `v` itself is counted (`gs_ge`), so `bit g v = 0`;
* `occ_zero`: on the upper face, separation `hSep g` (some coordinate at distance `≥ D` from every
  lower-face point) makes every summand vanish (`gs_zero_gen`), so `bit g v = 1`;
* `admissible`: hence the colouring satisfies the hypotheses of `Topology/SpernerCube`.
-/

namespace LeanProofs.IPRA.Topology.DimensionOccupancy

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm BigOperators
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Foundations.GridSums
open LeanProofs.IPRA.Foundations.GridSumsContext
open LeanProofs.IPRA.Foundations.GridSumsPoints
open LeanProofs.IPRA.Foundations.TermSums
open LeanProofs.IPRA.Topology.KuhnSimplices
open LeanProofs.IPRA.Topology.SpernerCube
open LeanProofs.IPRA.Topology.StaggeredGrids
open LeanProofs.IPRA.Topology.StaggeredCells (near dist)

set_option autoImplicit false

variable {n : ℕ}

/-! ## Packed lists of a fixed length -/

/-- `⟨f 0, ⟨f 1, …, ⟨f (k − 1), 0⟩⟩⟩`. -/
def pack : (k : ℕ) → (Fin k → PTm n) → PTm n
  | 0, _ => zero
  | k + 1, f => pairT (f 0) (pack k (fun i => f i.succ))

@[simp] theorem subst_pack {m : ℕ} (σ : Fin n → PTm m) :
    ∀ (k : ℕ) (f : Fin k → PTm n), Syn.subst σ (pack k f) = pack k (fun i => Syn.subst σ (f i))
  | 0, _ => by simp [pack]
  | k + 1, f => by simp [pack, subst_pack σ k]

theorem proj_pack {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (f : Fin k → PTm n) (i : Fin k), Γ ⊢[PRAAx] proj i.val (pack k f) ≐ f i
  | k + 1, f, ⟨0, _⟩ => fst_pair _ _
  | k + 1, f, ⟨i + 1, hi⟩ => (proj_pair_succ i _ _).eqTrans (proj_pack k _ ⟨i, by omega⟩)

theorem congrPack {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) {f f' : Fin k → PTm n}, (∀ i, Γ ⊢[PRAAx] f i ≐ f' i) → (Γ ⊢[PRAAx] pack k f ≐ pack k f')
  | 0, _, _, _ => .eqRefl _
  | k + 1, _, _, h => congrPairT (h 0) (congrPack k (fun i => h i.succ))

/-! ## Points pushed onto a base -/

theorem proj_pk_add {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (is : Fin k → PTm n) (x : PTm n) (r : ℕ), Γ ⊢[PRAAx] proj (k + r) (pk k is x) ≐ proj r x
  | 0, _, _, r => by rw [Nat.zero_add]; exact .eqRefl _
  | k + 1, is, x, r => by
    show Γ ⊢[PRAAx] proj (k + 1 + r) (pk k (fun r => is r.succ) (pairT (is 0) x)) ≐ proj r x
    rw [show k + 1 + r = k + (r + 1) by omega]
    exact (proj_pk_add k _ _ (r + 1)).eqTrans (proj_pair_succ r _ _)

theorem tl_pk_add {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (is : Fin k → PTm n) (x : PTm n) (r : ℕ), Γ ⊢[PRAAx] tl (k + r) (pk k is x) ≐ tl r x
  | 0, _, _, r => by rw [Nat.zero_add]; exact .eqRefl _
  | k + 1, is, x, r => by
    show Γ ⊢[PRAAx] tl (k + 1 + r) (pk k (fun r => is r.succ) (pairT (is 0) x)) ≐ tl r x
    rw [show k + 1 + r = k + (r + 1) by omega]
    exact (tl_pk_add k _ _ (r + 1)).eqTrans (tl_pair_succ r _ _)

theorem tl_pk {Γ : List (Fm PTm n)} (k : ℕ) (is : Fin k → PTm n) (x : PTm n) :
    Γ ⊢[PRAAx] tl k (pk k is x) ≐ x := tl_pk_add k is x 0

/-- Entry `q` of `pk k is x` is `is (k − 1 − q)`. -/
theorem proj_pk {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (is : Fin k → PTm n) (x : PTm n) (q : ℕ) (hq : q < k),
      Γ ⊢[PRAAx] proj q (pk k is x) ≐ is ⟨k - 1 - q, by omega⟩
  | k + 1, is, x, q, hq => by
    show Γ ⊢[PRAAx] proj q (pk k (fun r => is r.succ) (pairT (is 0) x)) ≐ _
    by_cases hqk : q < k
    · refine (proj_pk k _ _ q hqk).eqTrans ?_
      have e : (⟨k - 1 - q, by omega⟩ : Fin k).succ = ⟨k + 1 - 1 - q, by omega⟩ := by
        ext; simp; omega
      rw [e]; exact .eqRefl _
    · have hqk' : q = k := by omega
      subst hqk'
      have e : (⟨q + 1 - 1 - q, by omega⟩ : Fin (q + 1)) = 0 := by ext; simp
      rw [e]
      have h0 := proj_pk_add (Γ := Γ) q (fun r => is r.succ) (pairT (is 0) x) 0
      rw [Nat.add_zero] at h0
      exact h0.eqTrans (fst_pair _ _)

/-! ## Canonical repacking -/

theorem tl_canon {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (b v : PTm n), Γ ⊢[PRAAx] tl k (canon k b v) ≐ b
  | 0, _, _ => .eqRefl _
  | k + 1, b, v => (tl_pair_succ k _ _).eqTrans (tl_canon k b (sndT v))

theorem proj_canon {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (b v : PTm n) (q : ℕ), q < k → (Γ ⊢[PRAAx] proj q (canon k b v) ≐ proj q v)
  | k + 1, _, _, 0, _ => fst_pair _ _
  | k + 1, b, v, q + 1, hq => (proj_pair_succ q _ _).eqTrans (proj_canon k b (sndT v) q (by omega))

/-- `canon k b v` depends only on the first `k` entries of `v`. -/
theorem canon_congr {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (b : PTm n) {v v' : PTm n}, (∀ q, q < k → (Γ ⊢[PRAAx] proj q v ≐ proj q v')) →
      (Γ ⊢[PRAAx] canon k b v ≐ canon k b v')
  | 0, _, _, _, _ => .eqRefl _
  | k + 1, b, _, _, h => congrPairT (h 0 (by omega)) (canon_congr k b (fun q hq => h (q + 1) (by omega)))

theorem canon_base {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) {b b' : PTm n} (v : PTm n), (Γ ⊢[PRAAx] b ≐ b') → (Γ ⊢[PRAAx] canon k b v ≐ canon k b' v)
  | 0, _, _, _, h => h
  | k + 1, _, _, v, h => congrPairT (.eqRefl _) (canon_base k (sndT v) h)

theorem canon_idem {Γ : List (Fm PTm n)} (k : ℕ) (b v : PTm n) :
    Γ ⊢[PRAAx] canon k b (canon k b v) ≐ canon k b v :=
  canon_congr k b (fun q hq => proj_canon k b v q hq)

/-- A sum `≐ 0` has every term `≐ 0`. -/
theorem fsum_zero_elim {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (f : Fin k → PTm n), (Γ ⊢[PRAAx] fsum k f ≐ zero) → ∀ i, Γ ⊢[PRAAx] f i ≐ zero
  | 0, _, _, i => i.elim0
  | k + 1, f, h, i => by
    have h' : Γ ⊢[PRAAx] f 0 + fsum k (fun i => f i.succ) ≐ zero := by
      simpa [fsum, List.ofFn_succ, lsum] using h
    refine Fin.cases ?_ (fun i => ?_) i
    · exact add_eq_zero_left h'
    · exact fsum_zero_elim k _ (add_eq_zero_left ((add_comm _ _).eqTrans h')) i

/-! ## Grid points -/

/-- `v` is the code of a grid point of `G_D(N)` over `b`. -/
structure GridPt {m : ℕ} (D : ℕ) (Δ : List (Fm PTm m)) (b v : PTm m) : Prop where
  canon : Δ ⊢[PRAAx] v ≐ canon D b v
  bound : Δ ⊢[PRAAx] bsum D v b ≐ zero

theorem GridPt.tl {m D : ℕ} {Δ : List (Fm PTm m)} {b v : PTm m} (h : GridPt D Δ b v) :
    Δ ⊢[PRAAx] tl D v ≐ b :=
  (congrTl D h.canon).eqTrans (tl_canon D b v)

theorem GridPt.le {m D : ℕ} {Δ : List (Fm PTm m)} {b v : PTm m} (h : GridPt D Δ b v) (q : ℕ) (hq : q < D) :
    Δ ⊢[PRAAx] le (proj q v) (fstT b) :=
  fsum_zero_elim D _ h.bound ⟨q, hq⟩

/-- A list whose entries are `≤ N` gives a grid point after repacking over `b`. -/
theorem gridPt_canon {m D : ℕ} {Δ : List (Fm PTm m)} (b y : PTm m)
    (hle : ∀ q, q < D → (Δ ⊢[PRAAx] le (proj q y) (fstT b))) : GridPt D Δ b (canon D b y) :=
  ⟨(canon_idem D b y).eqSymm, fsum_eq_zero (fun q =>
    (congrMonus (proj_canon D b y q.val q.isLt) (.eqRefl _)).eqTrans (hle q.val q.isLt))⟩

theorem le_one_monus (t : PTm n) {Γ : List (Fm PTm n)} : Γ ⊢[PRAAx] le (monus one t) one := by
  refine .orE (zero_or_succ t) ?_ ?_
  · exact le_congr ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)).eqSymm (.eqRefl _) (le_refl _)
  · exact le_congr ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans ((succ_monus_succ _ _).eqTrans
      (zero_monus _))).eqSymm (.eqRefl _) (zero_le _)

theorem sg_one_of_pos {c : PTm n} {Γ : List (Fm PTm n)} (h : Γ ⊢[PRAAx] le one c) :
    Γ ⊢[PRAAx] Signum.sg c ≐ one := by
  have e : Γ ⊢[PRAAx] c ≐ succ (monus c one) := by
    ipra_lc natEq (eq_add_of_le h)
  exact (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) e)).eqTrans (Signum.sg_succ _)

/-! ## The occupancy scan, the bits and the colour -/

section Occupancy

variable (d' m : ℕ) (F : Fin m → PTm 1)

/-- The cells of `v` in grid `g`, packed. -/
def cellsOf (g : ℕ) (v : PTm n) : PTm n := pack m (fun j => cell d' g (col (F j) v))

/-- The base of the scan: `⟨N + 1, ⟨cells of v, b⟩⟩`. -/
def obase (g : ℕ) (v : PTm n) : PTm n :=
  pairT (succ (fstT (tl (d' + 1) v))) (pairT (cellsOf d' m F g v) (tl (d' + 1) v))

/-- The summand at a point `w` of `[0, N]^D`: `[w` on the lower face of coordinate `g]` times
`[the cells of w and v agree in grid g]`. -/
def occS (g : ℕ) : PTm 1 :=
  eqb (proj (d' - g) (Syn.var 0)) zero *
    fprod m (fun j => eqb (cell d' g (col (F j) (canon (d' + 1) (sndT (sndT (tl (d' + 1) (Syn.var 0))))
      (Syn.var 0)))) (proj j.val (fstT (sndT (tl (d' + 1) (Syn.var 0))))))

/-- The number of lower-face points of coordinate `g` in the grid-`g` cell of `v`. -/
def occ (g : ℕ) (v : PTm n) : PTm n := Syn.subst ![obase d' m F g v] (gs 0 (d' + 1) (occS d' m F g))

/-- `1` iff the grid-`g` cell of `v` holds no lower-face point. -/
def bit (g : ℕ) (v : PTm n) : PTm n := monus one (Signum.sg (occ d' m F g v))

/-- The colour `eq:color`: the number of leading unoccupied grids. -/
def lamT : PTm 1 :=
  Syn.subst (fun g : Fin (d' + 1) => bit d' m F g.val (Syn.var 0)) (LeadingBits.lamPat (d' + 1))

@[simp] theorem subst_cellsOf {k : ℕ} (σ : Fin n → PTm k) (g : ℕ) (v : PTm n) :
    Syn.subst σ (cellsOf d' m F g v) = cellsOf d' m F g (Syn.subst σ v) := by
  simp [cellsOf]

@[simp] theorem subst_obase {k : ℕ} (σ : Fin n → PTm k) (g : ℕ) (v : PTm n) :
    Syn.subst σ (obase d' m F g v) = obase d' m F g (Syn.subst σ v) := by
  simp [obase]

@[simp] theorem subst_occ {k : ℕ} (σ : Fin n → PTm k) (g : ℕ) (v : PTm n) :
    Syn.subst σ (occ d' m F g v) = occ d' m F g (Syn.subst σ v) := by
  simp only [occ, Syn.subst_subst]; congr 1; funext i; fin_cases i; simp

@[simp] theorem subst_bit {k : ℕ} (σ : Fin n → PTm k) (g : ℕ) (v : PTm n) :
    Syn.subst σ (bit d' m F g v) = bit d' m F g (Syn.subst σ v) := by
  simp [bit]

theorem col_lamT (v : PTm n) :
    col (lamT d' m F) v = Syn.subst (fun g : Fin (d' + 1) => bit d' m F g.val v) (LeadingBits.lamPat (d' + 1)) := by
  simp only [col, lamT, Syn.subst_subst]; congr 1; funext g; simp

theorem bit_le {Γ : List (Fm PTm n)} (g : ℕ) (v : PTm n) : Γ ⊢[PRAAx] le (bit d' m F g v) one :=
  le_one_monus _

/-! ### Lower faces: `v` is in its own scan -/

theorem occ_pos {Γ : List (Fm PTm n)} {b v : PTm n} (hv : GridPt (d' + 1) Γ b v) (g : ℕ) (hg : g ≤ d')
    (h0 : Γ ⊢[PRAAx] proj (d' - g) v ≐ zero) : Γ ⊢[PRAAx] le one (occ d' m F g v) := by
  let is : Fin (d' + 1) → PTm n := fun r => proj (d' - r.val) v
  let y := pk (d' + 1) is (obase d' m F g v)
  have hproj : ∀ q, q < d' + 1 → (Γ ⊢[PRAAx] proj q y ≐ proj q v) := fun q hq => by
    refine (proj_pk (d' + 1) is _ q hq).eqTrans ?_
    simp only [is]; rw [show d' - (d' + 1 - 1 - q) = q by omega]; exact .eqRefl _
  have htl : Γ ⊢[PRAAx] tl (d' + 1) y ≐ obase d' m F g v := tl_pk _ _ _
  have hb : Γ ⊢[PRAAx] sndT (sndT (tl (d' + 1) y)) ≐ b :=
    (congrSnd (congrSnd htl)).eqTrans ((congrSnd (snd_pair _ _)).eqTrans ((snd_pair _ _).eqTrans hv.tl))
  have hc : Γ ⊢[PRAAx] fstT (sndT (tl (d' + 1) y)) ≐ cellsOf d' m F g v :=
    (congrFst (congrSnd htl)).eqTrans (snd_pair _ _).fstE
  have hu : Γ ⊢[PRAAx] canon (d' + 1) (sndT (sndT (tl (d' + 1) y))) y ≐ v :=
    (canon_base (d' + 1) y hb).eqTrans ((canon_congr (d' + 1) b hproj).eqTrans hv.canon.eqSymm)
  have hS : Γ ⊢[PRAAx] Syn.subst ![y] (occS d' m F g) ≐ one := by
    simp only [occS, StaggeredGrids.cell, subst_ap2, PTm.subst_mul, subst_eqb, subst_fprod, subst_proj, subst_col, subst_canon,
      subst_tl, subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ, PTm.subst_add, PTm.subst_num]
    refine (congrMul (eqb_of_eq ((hproj (d' - g) (by omega)).eqTrans h0))
      (fprod_one (fun j => eqb_of_eq ?_))).eqTrans (one_mul _)
    exact (congrQuo (congrAdd (congrCol (F j) hu) (.eqRefl _))).eqTrans
      ((congrProj j.val hc).eqTrans (proj_pack m _ j)).eqSymm
  have hbound : ∀ r, Γ ⊢[PRAAx] lt (is r) (fstT (tl 0 (obase d' m F g v))) := fun r => by
    have hfst : Γ ⊢[PRAAx] fstT (obase d' m F g v) ≐ succ (fstT b) :=
      (fst_pair _ _).eqTrans (congrSucc (congrFst hv.tl))
    refine lt_congr (.eqRefl _) hfst.eqSymm ?_
    exact (succ_monus_succ _ _).eqTrans (hv.le (d' - r.val) (by omega))
  exact le_congr hS (.eqRefl _) (gs_ge (occS d' m F g) (d' + 1) 0 Γ (obase d' m F g v) is hbound)

theorem bit_zero {Γ : List (Fm PTm n)} {b v : PTm n} (hv : GridPt (d' + 1) Γ b v) (g : ℕ) (hg : g ≤ d')
    (h0 : Γ ⊢[PRAAx] proj (d' - g) v ≐ zero) : Γ ⊢[PRAAx] bit d' m F g v ≐ zero :=
  (congrMonus (.eqRefl _) (sg_one_of_pos (occ_pos d' m F hv g hg h0))).eqTrans (monus_self _)

/-! ### Separation -/

/-- Equal cells force distance `≤ d'`: `[dist(a, b) ≤ d'] = 1`. -/
theorem near_bit_of_cells {Γ : List (Fm PTm n)} (g : ℕ) {a b : PTm n}
    (h : Γ ⊢[PRAAx] cell d' g a ≐ cell d' g b) :
    Γ ⊢[PRAAx] monus one (monus (dist a b) (num d')) ≐ one := by
  refine .orE (lt_or_le (num d') (dist a b)) ?_ ?_
  · refine .botE _ (.orE (le_total a b) ?_ ?_)
    · -- `a ≤ b`: then `a + d ≤ b`
      let Δ₁ : List (Fm PTm n) := (le a b) :: (lt (num d') (dist a b)) :: Γ
      have hd : Δ₁ ⊢[PRAAx] dist a b ≐ monus b a := (congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (zero_add _)
      have h₁ := eq_add_of_le (Γ := Δ₁) Prf.hyp0
      have hlt : Δ₁ ⊢[PRAAx] lt (num d') (dist a b) := Prf.hyp1
      have h₂ := eq_add_of_le (le_congr (.eqRefl _) hd hlt)
      have hgap : Δ₁ ⊢[PRAAx] le (a + succ (num d')) b := by
        refine le_of_eq_add (d := monus (monus b a) (succ (num d'))) ?_
        have e₁ := natEq h₁; have e₂ := natEq h₂
        apply deriveNat; ipra_simps; linear_combination e₁ + e₂
      exact Prf.impE (cell_ne_of_gap d' g hgap) h.wk.wk
    · -- `b ≤ a`: then `b + d ≤ a`
      let Δ₁ : List (Fm PTm n) := (le b a) :: (lt (num d') (dist a b)) :: Γ
      have hd : Δ₁ ⊢[PRAAx] dist a b ≐ monus a b := (congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _)
      have h₁ := eq_add_of_le (Γ := Δ₁) Prf.hyp0
      have hlt : Δ₁ ⊢[PRAAx] lt (num d') (dist a b) := Prf.hyp1
      have h₂ := eq_add_of_le (le_congr (.eqRefl _) hd hlt)
      have hgap : Δ₁ ⊢[PRAAx] le (b + succ (num d')) a := by
        refine le_of_eq_add (d := monus (monus a b) (succ (num d'))) ?_
        have e₁ := natEq h₁; have e₂ := natEq h₂
        apply deriveNat; ipra_simps; linear_combination e₁ + e₂
      exact Prf.impE (cell_ne_of_gap d' g hgap) h.wk.wk.eqSymm
  · exact (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)

/-- The separation hypothesis body: grid points `u` on the lower and `v` on the upper face of
coordinate `g` have some target coordinate at distance `≥ D`. -/
def sepBody (g : ℕ) (u v b : PTm n) : Fm PTm n :=
  gridImp (d' + 1) u b (gridImp (d' + 1) v b ((proj (d' - g) u ≐ zero) ⟶ ((proj (d' - g) v ≐ fstT b) ⟶
    (fprod m (fun j => monus one (monus (dist (col (F j) u) (col (F j) v)) (num d'))) ≐ zero))))

/-- `eq:sep` for coordinate `g` (in units of `h/D`). -/
def hSep (g : ℕ) (b : PTm n) : Fm PTm n :=
  Fm.all (Fm.all (sepBody d' m F g (Syn.var 1) (Syn.var 0) (Syn.shift (Syn.shift b))))

@[simp] theorem subst_sepBody {k : ℕ} (σ : Fin n → PTm k) (g : ℕ) (u v b : PTm n) :
    (sepBody d' m F g u v b).subst σ = sepBody d' m F g (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ b) := by
  simp [sepBody]

@[simp] theorem subst_hSep {k : ℕ} (σ : Fin n → PTm k) (g : ℕ) (b : PTm n) :
    (hSep d' m F g b).subst σ = hSep d' m F g (Syn.subst σ b) := by
  simp [hSep, subst_up_shift', Syn.up]

theorem sep_at {Γ : List (Fm PTm n)} {g : ℕ} {b : PTm n} (h : Γ ⊢[PRAAx] hSep d' m F g b) (u v : PTm n) :
    Γ ⊢[PRAAx] sepBody d' m F g u v b := by
  have a := Prf.allE u h
  simp only [Fm.subst_all, subst_sepBody, Syn.subst_var] at a
  have a2 := Prf.allE v a
  simp only [subst_sepBody] at a2
  simpa [Syn.up, Syn.subst_inst_shift, subst_up_shift'] using a2

/-- The consequence of separation used in the scan: every lower-face point `u` of coordinate `g`
has a cell vector in grid `g` different from the stored one `c`. -/
def thetaF (g : ℕ) (b c : PTm n) : Fm PTm n :=
  Fm.all (gridImp (d' + 1) (Syn.var 0) (Syn.shift b) ((proj (d' - g) (Syn.var 0) ≐ zero) ⟶
    (fprod m (fun j => eqb (cell d' g (col (F j) (Syn.var 0))) (proj j.val (Syn.shift c))) ≐ zero)))

@[simp] theorem subst_thetaF {k : ℕ} (σ : Fin n → PTm k) (g : ℕ) (b c : PTm n) :
    (thetaF d' m F g b c).subst σ = thetaF d' m F g (Syn.subst σ b) (Syn.subst σ c) := by
  simp [thetaF, subst_up_shift', Syn.up]

theorem theta_at {Γ : List (Fm PTm n)} {g : ℕ} {b c u : PTm n} (h : Γ ⊢[PRAAx] thetaF d' m F g b c)
    (hu : GridPt (d' + 1) Γ b u) (h0 : Γ ⊢[PRAAx] proj (d' - g) u ≐ zero) :
    Γ ⊢[PRAAx] fprod m (fun j => eqb (cell d' g (col (F j) u)) (proj j.val c)) ≐ zero := by
  have a := Prf.allE u h
  simp only [StaggeredGrids.cell, subst_ap2, gridImp, Fm.subst_imp, Fm.subst_eq, subst_fprod, subst_eqb, subst_col,
    subst_proj, subst_canon, subst_bsum, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, PTm.subst_num,
    ConciseIPRA.PTm.subst_zero, PTm.subst_add, ConciseIPRA.PTm.subst_succ] at a
  exact .impE (.impE (.impE a hu.canon) hu.bound) h0

/-- Separation gives `Θ` for the cells of an upper-face point `v`. -/
theorem theta_of_sep {Γ : List (Fm PTm n)} {g : ℕ} {b v : PTm n} (hs : Γ ⊢[PRAAx] hSep d' m F g b)
    (hv : GridPt (d' + 1) Γ b v) (hN : Γ ⊢[PRAAx] proj (d' - g) v ≐ fstT b) :
    Γ ⊢[PRAAx] thetaF d' m F g b (cellsOf d' m F g v) := by
  refine .allI (.impI (.impI (.impI ?_)))
  let Δ : List (Fm PTm (n + 1)) := (proj (d' - g) (Syn.var 0) ≐ zero) ::
    (bsum (d' + 1) (Syn.var 0) (Syn.shift b) ≐ zero) ::
    (Syn.var 0 ≐ canon (d' + 1) (Syn.shift b) (Syn.var 0)) :: Γ.map Fm.shift
  have lift : ∀ {s t : PTm n}, (Γ ⊢[PRAAx] s ≐ t) → (Δ ⊢[PRAAx] Syn.shift s ≐ Syn.shift t) :=
    fun h => (eq_lift h _).wk.wk
  have hu : GridPt (d' + 1) Δ (Syn.shift b) (Syn.var 0) := ⟨hyp2, Prf.hyp1⟩
  have hv' : GridPt (d' + 1) Δ (Syn.shift b) (Syn.shift v) :=
    ⟨by simpa [Syn.shift] using lift hv.canon, by simpa [Syn.shift] using lift hv.bound⟩
  have hN' : Δ ⊢[PRAAx] proj (d' - g) (Syn.shift v) ≐ fstT (Syn.shift b) := by
    simpa [Syn.shift] using lift hN
  have hs' : Δ ⊢[PRAAx] hSep d' m F g (Syn.shift b) := by
    have e := hs.shift; simp only [Fm.shift, subst_hSep] at e; exact e.wk.wk.wk
  have hbits := Prf.impE (Prf.impE (Prf.impE (Prf.impE (Prf.impE (Prf.impE
    (sep_at d' m F hs' (Syn.var 0) (Syn.shift v)) hu.canon) hu.bound) hv'.canon) hv'.bound) Prf.hyp0) hN'
  -- the stored cells are those of `v`
  have hc : ∀ j : Fin m, Δ ⊢[PRAAx] proj j.val (Syn.shift (cellsOf d' m F g v)) ≐
      cell d' g (col (F j) (Syn.shift v)) := fun j => by
    rw [show Syn.shift (cellsOf d' m F g v) = cellsOf d' m F g (Syn.shift v) by simp [Syn.shift]]
    exact proj_pack m _ j
  refine (fprod_congr (fun j => congrEqb' (.eqRefl _) (hc j))).eqTrans ?_
  refine bit_product_zero
    (fun j : Fin m => eqb (cell d' g (col (F j) (Syn.var 0))) (cell d' g (col (F j) (Syn.shift v))))
    (fun _ => le_one_monus _) ?_
  intro Δ' hext hOne
  exact succ_ne_zero ((fprod_one (fun j => near_bit_of_cells d' g (eq_of_eqb (hOne j)))).eqSymm.eqTrans
    (hext _ hbits))

/-! ### Upper faces: the scan is empty -/

/-- Facts about the lists of the closed-grid scan: `Θ` at the base, the base, and entries `≤ N`. -/
def CFacts (g : ℕ) : ListFacts := fun e k Δ x =>
  ∃ b c : PTm k, (Δ ⊢[PRAAx] thetaF d' m F g b c) ∧
    (Δ ⊢[PRAAx] tl e x ≐ pairT (succ (fstT b)) (pairT c b)) ∧
    ∀ q, q < e → (Δ ⊢[PRAAx] lt (proj q x) (succ (fstT b)))

theorem cfacts_steps (g : ℕ) : Steps (CFacts d' m F g) 0 (d' + 1) := by
  intro e _ _ k Δ x ⟨b, c, hθ, htl, hq⟩
  let ψ : Fm PTm (k + 1) := lt (Syn.var 0) (Syn.shift (fstT (tl e x)))
  have htl' : (ψ :: Δ.map Fm.shift) ⊢[PRAAx] tl e (Syn.shift x) ≐
      pairT (succ (fstT (Syn.shift b))) (pairT (Syn.shift c) (Syn.shift b)) :=
    eqR (by simp [Syn.shift]) (eqL (shift_tl e x) (eq_lift htl ψ))
  refine ⟨Syn.shift b, Syn.shift c, ?_, (tl_pair_succ e _ _).eqTrans htl', fun q hq' => ?_⟩
  · have e' := hθ.shift; simp only [Fm.shift, subst_thetaF] at e'; exact e'.wk
  · cases q with
    | zero =>
      have hN : (ψ :: Δ.map Fm.shift) ⊢[PRAAx] Syn.shift (fstT (tl e x)) ≐ succ (fstT (Syn.shift b)) :=
        eqL (by rw [shift_fstT, shift_tl]) htl'.fstE
      exact lt_congr (fst_pair _ _).eqSymm hN Prf.hyp0
    | succ q =>
      have hp : (ψ :: Δ.map Fm.shift) ⊢[PRAAx]
          proj (q + 1) (pairT (Syn.var 0) (Syn.shift x)) ≐ Syn.shift (proj q x) :=
        eqR (shift_proj q x).symm (proj_pair_succ q (Syn.var 0) (Syn.shift x))
      exact lt_congr hp.eqSymm (.eqRefl _) (ltR (by simp [Syn.shift]) (lt_lift (hq q (by omega)) ψ))

set_option maxHeartbeats 1000000 in
theorem occ_zero {Γ : List (Fm PTm n)} {g : ℕ} {b v : PTm n}
    (hθ : Γ ⊢[PRAAx] thetaF d' m F g b (cellsOf d' m F g v)) (hv : Γ ⊢[PRAAx] tl (d' + 1) v ≐ b) :
    Γ ⊢[PRAAx] occ d' m F g v ≐ zero := by
  have h0 : CFacts d' m F g 0 n Γ (obase d' m F g v) :=
    ⟨b, cellsOf d' m F g v, hθ,
      congrPairT (congrSucc (congrFst hv)) (congrPairT (.eqRefl _) hv), fun q hq => absurd hq (by omega)⟩
  refine gs_zero_gen (cfacts_steps d' m F g) (fun k Δ y hy => ?_) (d' + 1) 0 (by omega) le_rfl Γ
    (obase d' m F g v) h0
  obtain ⟨b, c, hθ', htl, hq⟩ := hy
  have hu : GridPt (d' + 1) Δ b (canon (d' + 1) b y) :=
    gridPt_canon b y (fun q hq' => Foundations.BoundedDecision.le_of_lt_succ (hq q hq'))
  have hb : Δ ⊢[PRAAx] sndT (sndT (tl (d' + 1) y)) ≐ b :=
    (congrSnd (congrSnd htl)).eqTrans (snd_pair _ _).sndE
  have hc : Δ ⊢[PRAAx] fstT (sndT (tl (d' + 1) y)) ≐ c :=
    (congrFst (congrSnd htl)).eqTrans (snd_pair _ _).fstE
  have hcan : Δ ⊢[PRAAx] canon (d' + 1) (sndT (sndT (tl (d' + 1) y))) y ≐ canon (d' + 1) b y :=
    canon_base (d' + 1) y hb
  simp only [occS, StaggeredGrids.cell, subst_ap2, PTm.subst_mul, subst_eqb, subst_fprod, subst_proj, subst_col, subst_canon,
    subst_tl, subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ, PTm.subst_add, PTm.subst_num]
  refine (congrMul (.eqRefl _) (fprod_congr (fun j => congrEqb'
    (congrQuo (congrAdd (congrCol (F j) hcan) (.eqRefl _))) (congrProj j.val hc)))).eqTrans ?_
  refine .orE (eqb01' (proj (d' - g) y) zero) ?_ ?_
  · exact (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
  · have h0 : ((eqb (proj (d' - g) y) zero ≐ one) :: Δ) ⊢[PRAAx] proj (d' - g) (canon (d' + 1) b y) ≐ zero :=
      (proj_canon (d' + 1) b y (d' - g) (by omega)).eqTrans (eq_of_eqb Prf.hyp0)
    exact (congrMul (.eqRefl _) (theta_at d' m F hθ'.wk ⟨hu.canon.wk, hu.bound.wk⟩ h0)).eqTrans (mul_zero _)

/-! ### The colouring is admissible -/

theorem bit_one {Γ : List (Fm PTm n)} {g : ℕ} {b v : PTm n} (hs : Γ ⊢[PRAAx] hSep d' m F g b)
    (hv : GridPt (d' + 1) Γ b v) (hN : Γ ⊢[PRAAx] proj (d' - g) v ≐ fstT b) :
    Γ ⊢[PRAAx] bit d' m F g v ≐ one :=
  (congrMonus (.eqRefl _) ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _)
    (occ_zero d' m F (theta_of_sep d' m F hs hv hN) hv.tl))).eqTrans Signum.sg_zero)).eqTrans (monus_zero _)

/-- With separation for every coordinate, the occupancy colouring satisfies the hypotheses of
`Topology/SpernerCube`. -/
theorem admissible {Γ : List (Fm PTm n)} {b : PTm n} (hs : ∀ g, g ≤ d' → (Γ ⊢[PRAAx] hSep d' m F g b)) :
    Hyps (d' + 1) (lamT d' m F) Γ b := by
  have hs' : ∀ g, g ≤ d' → ∀ (ψ₁ ψ₂ ψ₃ : Fm PTm (n + 1)),
      (ψ₁ :: ψ₂ :: ψ₃ :: Γ.map Fm.shift) ⊢[PRAAx] hSep d' m F g (Syn.shift b) := fun g hg _ _ _ => by
    have e := (hs g hg).shift; simp only [Fm.shift, subst_hSep] at e; exact e.wk.wk.wk
  refine ⟨.allI (.impI (.impI ?_)), fun j hj => .allI (.impI (.impI (.impI ?_))),
    fun j hj => .allI (.impI (.impI (.impI ?_)))⟩
  · rw [col_lamT]
    exact LeadingBits.range_at _ (fun g => bit_le d' m F g.val _)
  · have hg : d' - (d' - j) = j := by omega
    have hb := bit_zero d' m F (Γ := (proj j (Syn.var 0) ≐ zero) :: (bsum (d' + 1) (Syn.var 0) (Syn.shift b) ≐ zero) ::
        (Syn.var 0 ≐ canon (d' + 1) (Syn.shift b) (Syn.var 0)) :: Γ.map Fm.shift)
      (b := Syn.shift b) (v := Syn.var 0) ⟨hyp2, Prf.hyp1⟩ (d' - j) (by omega)
      (by rw [hg]; exact Prf.hyp0)
    have r := LeadingBits.low_at (D := d' + 1) _ (fun g => bit_le d' m F g.val (Syn.var 0)) ⟨d' - j, by omega⟩ hb
    rw [col_lamT, show d' + 1 - 1 - j = d' - j by omega]
    exact r
  · have hg : d' - (d' - j) = j := by omega
    have hb := bit_one d' m F (b := Syn.shift b) (v := Syn.var 0) (hs' (d' - j) (by omega) _ _ _)
      ⟨hyp2, Prf.hyp1⟩ (by rw [hg]; exact Prf.hyp0)
    have r := LeadingBits.up_at (D := d' + 1) _ (fun g => bit_le d' m F g.val (Syn.var 0)) ⟨d' - j, by omega⟩ hb
    rw [col_lamT, show d' + 1 - 1 - j = d' - j by omega]
    exact r

end Occupancy

end LeanProofs.IPRA.Topology.DimensionOccupancy
