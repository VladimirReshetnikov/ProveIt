import IPRADerivations.Topology.DimensionOccupancy

/-!
# The finite dimension obstruction in every dimension (`dimension_invariance_ipra`, `thm:finite`)

Packet: `topology/dimension_invariance_ipra`, `thm:finite`: "If `d > 0`, `N ≥ 1`, `h > 0`, and the
rational table `F` satisfies `eq:sep` and `eq:small`, then `d ≤ m`." Here for every dimension
`D = d' + 1` and every `m < D`, with the table in natural units of `h/D` as in
`Topology/DimensionTwo` (the case `D = 2`, `m = 1`): `m` terms `F j` in the packed point of the grid
`G_D(N)` over the base `b = ⟨N, p⟩`,

* `hSep g` (`Topology/DimensionOccupancy`): for grid points `u` with coordinate `g` equal to `0` and
  `v` with coordinate `g` equal to `N`, some `F j` differs by at least `D` (`eq:sep`, distance `≥ h`);
* `hSmall`: for every base point `a ∈ [0, N)^D` and every Kuhn simplex `(a, π)`, the values of each
  `F j` at any two vertices differ by at most `1` (`eq:small`, distance `≤ h/D`; the packet's strict
  bound `< h/D` implies it);

and `no_table`: these hypotheses are contradictory when `m < D` (for `D ≤ m` there is nothing to
prove). `dimension_obstruction` is the closed sentence for every `d'`, `m < d' + 1` and table.

The proof is the packet's. The occupancy colouring is admissible (`DimensionOccupancy.admissible`),
so `Topology/SpernerCube` gives an odd number of full Kuhn simplices. Conversely no simplex is full
(`no_full`): the colours of its vertices are split over all numeral values
(`Foundations/BoundedCases`); a non-exact colouring gives `[full] = 0` by evaluation, and for an
exact one the vertex `u_g` of colour `g < D` is occupied in grid `g` while the vertex `w` of colour
`D` is not, so their cell vectors differ in grid `g` at some coordinate; by
`StaggeredGrids.staggered_grid` no coordinate serves two grids, and `StaggeredGrids.pigeon` forbids
this for `m < D`. The count is then both odd and `0`. No witness is extracted
(the witness of `thm:alternative` is `Topology/DimensionAlternative`). The rational version (a rescaling of the table) is
`Topology/DimensionRational`.
-/

namespace LeanProofs.IPRA.Topology.DimensionObstruction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm BigOperators
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Foundations.GridSums
open LeanProofs.IPRA.Foundations.GridSumsContext
open LeanProofs.IPRA.Foundations.TermSums
open LeanProofs.IPRA.Foundations.BoundedCases
open LeanProofs.IPRA.Topology.KuhnSimplices
open LeanProofs.IPRA.Topology.SpernerCube
open LeanProofs.IPRA.Topology.StaggeredGrids
open LeanProofs.IPRA.Topology.StaggeredCells (near near_of_dist dist)
open LeanProofs.IPRA.Topology.DimensionOccupancy
open Equiv

set_option autoImplicit false

variable {n : ℕ}

/-! ## Sums of zero -/

theorem lsum_zero_elim {Γ : List (Fm PTm n)} :
    ∀ (l : List (PTm n)), (Γ ⊢[PRAAx] lsum l ≐ zero) → ∀ t, t ∈ l → (Γ ⊢[PRAAx] t ≐ zero)
  | [], _, _, ht => absurd ht (List.not_mem_nil)
  | a :: l, h, t, ht => by
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact add_eq_zero_left h
    · exact lsum_zero_elim l (add_eq_zero_left ((add_comm _ _).eqTrans h)) t ht'

theorem ftsum_zero_elim {Γ : List (Fm PTm n)} {ι : Type} [Fintype ι] {f : ι → PTm n}
    (h : Γ ⊢[PRAAx] ftsum f ≐ zero) (i : ι) : Γ ⊢[PRAAx] f i ≐ zero :=
  lsum_zero_elim _ h (f i) (List.mem_map.2 ⟨i, Finset.mem_toList.2 (Finset.mem_univ i), rfl⟩)

theorem ftsum_zero {Γ : List (Fm PTm n)} {ι : Type} [Fintype ι] {f : ι → PTm n}
    (h : ∀ i, Γ ⊢[PRAAx] f i ≐ zero) : Γ ⊢[PRAAx] ftsum f ≐ zero :=
  (ftsum_congr (g := fun _ => zero) h).eqTrans (of_mk (by rw [mk_ftsum]; simp))

/-! ## The small-simplex hypothesis -/

section Small

variable (d' m : ℕ) (F : Fin m → PTm 1)

/-- The strict bound `Σ_q ((x_q + 1) ∸ N) = 0`: a base point of `[0, N)^D`. -/
def bsumLt (k : ℕ) (v b : PTm n) : PTm n := fsum k (fun q => monus (succ (proj q.val v)) (fstT b))

/-- `Σ_{π, s, t, j} (|F_j(v_s) − F_j(v_t)| ∸ 1)` for the simplices at `a`. -/
noncomputable def smallSum (a : PTm n) : PTm n :=
  ftsum (fun π : Perm (Fin (d' + 1)) => fsum (d' + 2) (fun s => fsum (d' + 2) (fun t => fsum m (fun j =>
    monus (dist (col (F j) (vert (d' + 1) π s.val a)) (col (F j) (vert (d' + 1) π t.val a))) one))))

/-- `eq:small` at every base point. -/
noncomputable def hSmall (b : PTm n) : Fm PTm n :=
  Fm.all ((Syn.var 0 ≐ canon (d' + 1) (Syn.shift b) (Syn.var 0)) ⟶
    ((bsumLt (d' + 1) (Syn.var 0) (Syn.shift b) ≐ zero) ⟶ (smallSum d' m F (Syn.var 0) ≐ zero)))

@[simp] theorem subst_bsumLt {k' : ℕ} (σ : Fin n → PTm k') (k : ℕ) (v b : PTm n) :
    Syn.subst σ (bsumLt k v b) = bsumLt k (Syn.subst σ v) (Syn.subst σ b) := by
  simp [bsumLt]

@[simp] theorem subst_smallSum {k : ℕ} (σ : Fin n → PTm k) (a : PTm n) :
    Syn.subst σ (smallSum d' m F a) = smallSum d' m F (Syn.subst σ a) := by
  simp [smallSum]

@[simp] theorem subst_hSmall {k : ℕ} (σ : Fin n → PTm k) (b : PTm n) :
    (hSmall d' m F b).subst σ = hSmall d' m F (Syn.subst σ b) := by
  simp [hSmall, subst_up_shift', Syn.up]

theorem small_at {Γ : List (Fm PTm n)} {b a : PTm n} (h : Γ ⊢[PRAAx] hSmall d' m F b)
    (h₁ : Γ ⊢[PRAAx] a ≐ canon (d' + 1) b a) (h₂ : Γ ⊢[PRAAx] bsumLt (d' + 1) a b ≐ zero) :
    Γ ⊢[PRAAx] smallSum d' m F a ≐ zero := by
  have e := Prf.allE a h
  simp only [Fm.subst_imp, Fm.subst_eq, subst_canon, subst_bsumLt, subst_smallSum,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at e
  exact .impE (.impE e h₁) h₂

/-- Two vertices of a simplex at a base point are within `1` in every target coordinate. -/
theorem near_of_small {Γ : List (Fm PTm n)} {a : PTm n} (h : Γ ⊢[PRAAx] smallSum d' m F a ≐ zero)
    (π : Perm (Fin (d' + 1))) (s t : Fin (d' + 2)) (j : Fin m) :
    Γ ⊢[PRAAx] le (dist (col (F j) (vert (d' + 1) π s.val a)) (col (F j) (vert (d' + 1) π t.val a))) one :=
  fsum_zero_elim m _ (fsum_zero_elim (d' + 2) _ (fsum_zero_elim (d' + 2) _ (ftsum_zero_elim h π) s) t) j

end Small

/-! ## Repacking a base list does not move the vertices -/

theorem incr_canon_eq {Γ : List (Fm PTm n)} :
    ∀ (k : ℕ) (bits : ℕ → Bool) (y b : PTm n), (Γ ⊢[PRAAx] tl k y ≐ b) →
      (Γ ⊢[PRAAx] incr k bits (canon k b y) ≐ incr k bits y)
  | 0, _, _, _, h => h.eqSymm
  | k + 1, bits, y, b, h => by
    simp only [incr, canon]
    exact congrPairT (congrBump _ (fst_pair _ _))
      ((congrIncr k _ (snd_pair _ _)).eqTrans (incr_canon_eq k _ (sndT y) b h))

theorem congrDist {Γ : List (Fm PTm n)} {a a' c c' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] c ≐ c') :
    Γ ⊢[PRAAx] dist a c ≐ dist a' c' :=
  congrAdd (congrMonus h₁ h₂) (congrMonus h₂ h₁)

/-! ## Facts carried into the full count -/

section Count

variable (d' m : ℕ) (F : Fin m → PTm 1)

/-- The hypotheses at the base `b`, the base, and entries `< N`. -/
noncomputable def OFacts : ListFacts := fun e k Δ x =>
  ∃ b : PTm k, (∀ g, g ≤ d' → (Δ ⊢[PRAAx] hSep d' m F g b)) ∧ (Δ ⊢[PRAAx] hSmall d' m F b) ∧
    (Δ ⊢[PRAAx] tl e x ≐ b) ∧ ∀ q, q < e → (Δ ⊢[PRAAx] lt (proj q x) (fstT b))

theorem ofacts_steps : Steps (OFacts d' m F) 0 (d' + 1) := by
  intro e _ _ k Δ x ⟨b, hs, hsm, htl, hq⟩
  let ψ : Fm PTm (k + 1) := lt (Syn.var 0) (Syn.shift (fstT (tl e x)))
  have htl' : (ψ :: Δ.map Fm.shift) ⊢[PRAAx] tl e (Syn.shift x) ≐ Syn.shift b :=
    eqL (shift_tl e x) (eq_lift htl ψ)
  refine ⟨Syn.shift b, fun g hg => ?_, ?_, (tl_pair_succ e _ _).eqTrans htl', fun q hq' => ?_⟩
  · have e' := (hs g hg).shift; simp only [Fm.shift, subst_hSep] at e'; exact e'.wk
  · have e' := hsm.shift; simp only [Fm.shift, subst_hSmall] at e'; exact e'.wk
  · cases q with
    | zero =>
      have hN : (ψ :: Δ.map Fm.shift) ⊢[PRAAx] Syn.shift (fstT (tl e x)) ≐ fstT (Syn.shift b) :=
        eqL (by rw [shift_fstT, shift_tl]) (congrFst htl')
      exact lt_congr (fst_pair _ _).eqSymm hN Prf.hyp0
    | succ q =>
      have hp : (ψ :: Δ.map Fm.shift) ⊢[PRAAx]
          proj (q + 1) (pairT (Syn.var 0) (Syn.shift x)) ≐ Syn.shift (proj q x) :=
        eqR (shift_proj q x).symm (proj_pair_succ q (Syn.var 0) (Syn.shift x))
      exact lt_congr hp.eqSymm (.eqRefl _) (ltR (shift_fstT b) (lt_lift (hq q (by omega)) ψ))

/-- A `0/1` term with `1 ∸ s = 0` is `1`; with `1 ∸ s = 1` it is `0`. -/
theorem bit_cases {Γ : List (Fm PTm n)} {s : PTm n} (hs : Γ ⊢[PRAAx] le s one) :
    Γ ⊢[PRAAx] s + monus one s ≐ one :=
  Foundations.BoundedDecision.bounded_decide 1 (Syn.var 0 + monus one (Syn.var 0) : PTm 1) one
    (fun ρ hρ => by have := hρ 0; simp; omega) ![s] (fun i => by fin_cases i; exact hs) |>
    fun e => by simpa using e

/-- No Kuhn simplex is full. -/
theorem no_full (hdm : m < d' + 1) {k : ℕ} {Δ : List (Fm PTm k)} {y : PTm k}
    (hy : OFacts d' m F (d' + 1) k Δ y) (π : Perm (Fin (d' + 1))) :
    Δ ⊢[PRAAx] fullT (d' + 1) (lamT d' m F) π y ≐ zero := by
  obtain ⟨b, hs, hsm, htl, hq⟩ := hy
  have hH := admissible d' m F hs
  -- every vertex is a grid point over `b`
  have hgrid : ∀ s : ℕ, GridPt (d' + 1) Δ b (vert (d' + 1) π s y) := fun s => by
    obtain ⟨h₁, h₂⟩ := incr_grid (d' + 1) (vbit (d' + 1) π s) y b htl (fun q hq' => le_of_lt (hq q hq'))
      (fun q hq' _ => hq q hq')
    exact ⟨h₁, h₂⟩
  have htlv : ∀ s : ℕ, Δ ⊢[PRAAx] tl (d' + 1) (vert (d' + 1) π s y) ≐ tl (d' + 1) y := fun s => tl_incr _ _ _
  -- the base point and the small-simplex condition there
  have hsmall := small_at d' m F hsm (a := canon (d' + 1) b y) (canon_idem (d' + 1) b y).eqSymm
    (fsum_eq_zero (fun q => (congrMonus (congrSucc (proj_canon (d' + 1) b y q.val q.isLt)) (.eqRefl _)).eqTrans
      (hq q.val q.isLt)))
  have hnear : ∀ (s t : Fin (d' + 2)) (j : Fin m),
      Δ ⊢[PRAAx] near (col (F j) (vert (d' + 1) π s.val y)) (col (F j) (vert (d' + 1) π t.val y)) :=
    fun s t j => near_of_dist (le_congr (congrDist (congrCol (F j) (incr_canon_eq _ _ y b htl))
      (congrCol (F j) (incr_canon_eq _ _ y b htl))) (.eqRefl _) (near_of_small d' m F hsmall π s t j))
  -- the colours are `≤ D`
  let κ : Fin (d' + 2) → PTm k := cols (d' + 1) (lamT d' m F) π y
  have hκle : ∀ s, Δ ⊢[PRAAx] le (κ s) (num (d' + 1)) := fun s => range_at hH.1 (hgrid s.val).canon (hgrid s.val).bound
  refine bounded_cases (d' + 1) κ _ hκle (fun ρ hρ Δ' hext hκ => ?_)
  by_cases hex : ∀ j : Fin (d' + 2), cntV ρ j.val = 1
  · -- an exact colouring is impossible
    refine .botE _ ?_
    have hsOf : ∀ g : Fin (d' + 2), ∃ s : Fin (d' + 2), ρ s = g.val := fun g => by
      have h1 := hex g
      rw [cnt_card, Finset.card_eq_one] at h1
      obtain ⟨s, hs'⟩ := h1
      have hm : s ∈ ({s} : Finset (Fin (d' + 2))) := Finset.mem_singleton_self s
      rw [← hs', Finset.mem_filter] at hm
      exact ⟨s, hm.2⟩
    choose sOf hsOf using hsOf
    let u : Fin (d' + 1) → PTm k := fun g => vert (d' + 1) π (sOf g.castSucc).val y
    let w : PTm k := vert (d' + 1) π (sOf (Fin.last (d' + 1))).val y
    let bits : PTm k → Fin (d' + 1) → PTm k := fun v g => bit d' m F g.val v
    have hcol : ∀ s : Fin (d' + 2), Δ' ⊢[PRAAx] col (lamT d' m F) (vert (d' + 1) π s.val y) ≐ num (ρ s) := hκ
    -- the vertex of colour `g` is occupied in grid `g`, the vertex of colour `D` is not
    have hu0 : ∀ g : Fin (d' + 1), Δ' ⊢[PRAAx] bit d' m F g.val (u g) ≐ zero := fun g => by
      have e := LeadingBits.colour_bit (Γ := Δ') (bits (u g)) (fun g' => bit_le d' m F g'.val _) g
      have h1 : Δ' ⊢[PRAAx] eqb (Syn.subst (bits (u g)) (LeadingBits.lamPat (d' + 1))) (num g.val) ≐ one := by
        refine eqb_of_eq ?_
        have := hcol (sOf g.castSucc)
        rw [hsOf g.castSucc, col_lamT, Fin.val_castSucc] at this
        exact this
      exact (one_mul _).eqSymm.eqTrans ((congrMul h1.eqSymm (.eqRefl _)).eqTrans e)
    have hw1 : ∀ g : Fin (d' + 1), Δ' ⊢[PRAAx] bit d' m F g.val w ≐ one := fun g => by
      have e := LeadingBits.top_bit (Γ := Δ') (bits w) (fun g' => bit_le d' m F g'.val _) g
      have h1 : Δ' ⊢[PRAAx] eqb (Syn.subst (bits w) (LeadingBits.lamPat (d' + 1))) (num (d' + 1)) ≐ one := by
        refine eqb_of_eq ?_
        have := hcol (sOf (Fin.last (d' + 1)))
        rw [hsOf (Fin.last (d' + 1)), col_lamT, Fin.val_last] at this
        exact this
      have h2 : Δ' ⊢[PRAAx] le one (bit d' m F g.val w) :=
        (one_mul _).eqSymm.eqTrans ((congrMul h1.eqSymm (.eqRefl _)).eqTrans e)
      exact le_antisymm (bit_le d' m F g.val w) h2
    -- different occupancy forces different cells
    have hcells : ∀ (g : Fin (d' + 1)) (Δ'' : List (Fm PTm k)), Extends Δ' Δ'' → (∀ j : Fin m, Δ'' ⊢[PRAAx]
        cell d' g.val (col (F j) (u g)) ≐ cell d' g.val (col (F j) w)) → (Δ'' ⊢[PRAAx] Fm.bot) := by
      intro g Δ'' hext'' hc
      have hob : Δ'' ⊢[PRAAx] obase d' m F g.val (u g) ≐ obase d' m F g.val w := by
        have ht : Δ'' ⊢[PRAAx] tl (d' + 1) (u g) ≐ tl (d' + 1) w :=
          (hext'' _ (hext _ (htlv _))).eqTrans (hext'' _ (hext _ (htlv _))).eqSymm
        exact congrPairT (congrSucc (congrFst ht)) (congrPairT (congrPack m hc) ht)
      have hocc : Δ'' ⊢[PRAAx] occ d' m F g.val (u g) ≐ occ d' m F g.val w := Foundations.GridSums.congr1 _ hob
      have hb : Δ'' ⊢[PRAAx] bit d' m F g.val (u g) ≐ bit d' m F g.val w :=
        congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hocc))
      exact succ_ne_zero ((hext'' _ (hw1 g)).eqSymm.eqTrans (hb.eqSymm.eqTrans (hext'' _ (hu0 g))))
    -- the injection count
    let Dm : Fin (d' + 1) → Fin m → PTm k := fun g j =>
      monus one (eqb (cell d' g.val (col (F j) (u g))) (cell d' g.val (col (F j) w)))
    refine pigeon hdm Dm (fun g j => le_one_monus _) (fun g => ?_) (fun j g g' hgg => ?_)
    · -- some coordinate separates the cells of `u g` and `w`
      refine mapped_bit_product_zero
        (fun j : Fin m => eqb (cell d' g.val (col (F j) (u g))) (cell d' g.val (col (F j) w)))
        _ (fun _ => le_one_monus _) ?_ ?_
      · intro Δ'' hext' hOne
        exact hcells g Δ'' hext' (fun j => eq_of_eqb (hOne j))
      · intro j
        exact .impI ((congrMonus (.eqRefl _) (StaggeredGrids.monus_one_zero Prf.hyp0)).eqTrans (monus_self _))
    · -- no coordinate separates two grids
      have hgg' : g.val < g'.val := hgg
      have stag := staggered_grid (Γ := Δ') d' g.val g'.val hgg' g'.isLt
        (u := col (F j) (u g)) (v := col (F j) (u g')) (w := col (F j) w)
        (hext _ (hnear (sOf g.castSucc) (sOf (Fin.last (d' + 1))) j))
        (hext _ (hnear (sOf g'.castSucc) (sOf (Fin.last (d' + 1))) j))
        (hext _ (hnear (sOf g.castSucc) (sOf g'.castSucc) j))
      refine .orE stag ?_ ?_
      · exact (congrMul ((congrMonus (.eqRefl _) (eqb_of_eq Prf.hyp0)).eqTrans (monus_self _))
          (.eqRefl _)).eqTrans (zero_mul _)
      · exact (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) (eqb_of_eq Prf.hyp0)).eqTrans
          (monus_self _))).eqTrans (mul_zero _)
  · -- otherwise `[full] = 0` by evaluation
    have e := Foundations.BoundedDecision.decide_at (exactPat (d' + 2)) zero κ ρ hκ (by
      rw [ev_exactPat, exactV_eq, if_neg hex]; rfl)
    simpa [fullT] using e

/-- `thm:finite` in natural units: separation for every coordinate and small simplices are
contradictory when `m < D`. -/
theorem no_table (hdm : m < d' + 1) {Γ : List (Fm PTm n)} {b : PTm n}
    (hs : ∀ g, g ≤ d' → (Γ ⊢[PRAAx] hSep d' m F g b)) (hsm : Γ ⊢[PRAAx] hSmall d' m F b) :
    Γ ⊢[PRAAx] Fm.bot := by
  have hpar := sperner_parity (d' + 1) (lamT d' m F) Γ b (admissible d' m F hs)
  have hzero : Γ ⊢[PRAAx] count (d' + 1) (lamT d' m F) b ≐ zero := by
    refine gs_zero_gen (ofacts_steps d' m F) (fun k Δ y hy => ?_) (d' + 1) 0 (by omega) le_rfl Γ b
      ⟨b, hs, hsm, .eqRefl _, fun q hq => absurd hq (by omega)⟩
    simp only [fullS, subst_ftsum, subst_fullT, Syn.subst_var, Matrix.cons_val_zero]
    exact ftsum_zero (fun π => no_full d' m F hdm hy π)
  exact succ_ne_zero (hpar.eqSymm.eqTrans ((congrAp1 parF hzero).eqTrans par_zero))

end Count

/-! ## The closed sentence -/

section Closed

variable (d' m : ℕ) (F : Fin m → PTm 1)

/-- The hypotheses at the base `⟨N, p⟩`: separation for every coordinate, small simplices. -/
noncomputable def obstructionHyps : List (Fm PTm 2) :=
  List.ofFn (fun g : Fin (d' + 1) => hSep d' m F g.val base2) ++ [hSmall d' m F base2]

/-- `∀ N p. ¬ (eq:sep ∧ eq:small)` for a table to `m < D` coordinates. -/
noncomputable def obstructionFormula : Fm PTm 2 := impAll (obstructionHyps d' m F) Fm.bot

/-- `thm:finite` for every dimension `D = d' + 1`, every `m < D` and every table, as a closed
sentence of iPRA. -/
theorem dimension_obstruction (hdm : m < d' + 1) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (obstructionFormula d' m F) := by
  refine closeUniv 2 (impAll_intro _ _ _ (no_table d' m F hdm (b := base2) (fun g hg => .hyp ?_) (.hyp ?_)))
  · simp only [obstructionHyps, List.append_nil, List.mem_reverse, List.mem_append, List.mem_ofFn,
      List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl ⟨⟨g, by omega⟩, rfl⟩
  · simp [obstructionHyps]

end Closed

end LeanProofs.IPRA.Topology.DimensionObstruction
