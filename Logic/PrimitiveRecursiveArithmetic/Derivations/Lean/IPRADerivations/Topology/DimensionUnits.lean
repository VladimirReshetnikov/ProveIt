import IPRADerivations.DiophantineNumberTheory.Dirichlet
import IPRADerivations.Topology.DimensionTwo

/-!
# The dimension obstruction for tables in an arbitrary unit (`thm:finite`, `d = 2`, `h = 2M`)

Packet: `topology/dimension_invariance_ipra`, `thm:finite` with `eq:sep` and `eq:small` in the
packet's own scale. `DimensionTwo.no_table` is stated for tables in units of `h / 2`. Here the
table is an arbitrary ternary primitive recursive symbol `F(x, y, p)` with natural-number
values, and the separation is `h = 2M` for a variable `M ≥ 1`, so that `h / d = M`:

* `usep0F`, `usep1F` (`eq:sep`): opposite faces have values at distance `≥ 2M`;
* `usmallF` (`eq:small`, strict): the vertices of each Kuhn triangle have values at distance
  `< M`;
* `no_table_units`, `no_table_units_closed`: for all `N`, `M ≥ 1` and `p` the three conditions
  are contradictory.

The reduction passes to the table `⌊F / M⌋`, an explicit symbol `GF` with the packed parameter
`⟨M, p⟩`:

* `quo_far`: `|a − b| ≥ 2M` gives `|⌊a/M⌋ − ⌊b/M⌋| ≥ 2`;
* `quo_near`, `dist_le_one_of_near`: `|a − b| < M` gives `|⌊a/M⌋ − ⌊b/M⌋| ≤ 1`.

A rational table with a common denominator `D`, bounded below, and a rational `h` are of this
form after a translation and multiplication by `2 D` times the denominator of `h`; that
normalization of the input is not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.DimensionUnits

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.Dirichlet (quo_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)
open LeanProofs.IPRA.Topology.Sperner2D
open LeanProofs.IPRA.Topology.StaggeredCells
open LeanProofs.IPRA.Topology.DimensionTwo

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Floors and distances -/

alias pos_succ := Common.pos_of_one_le

/-- `⌊(z + M) / M⌋ = ⌊z / M⌋ + 1`. -/
theorem quo_add_self {z M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] quo (z + M) M ≐ succ (quo z M) := by
  have d := div_mod_at (Γ := Γ) (x := z) hM
  refine quo_eq hM ?_ (.andE₂ d)
  ipra_lc natEq (Prf.andE₁ d)

theorem dist_of_add {X Y e : PTm n} (h : Γ ⊢[PRAAx] X ≐ Y + e) : Γ ⊢[PRAAx] dist X Y ≐ e :=
  (congrAdd ((congrMonus h (.eqRefl _)).eqTrans (add_monus' _ _))
    ((congrMonus (.eqRefl _) h).eqTrans (monus_add _ _))).eqTrans (add_zero _)

theorem dist_comm (a b : PTm n) : Γ ⊢[PRAAx] dist a b ≐ dist b a := add_comm _ _

theorem dist_congr {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] dist a b ≐ dist a' b' :=
  congrAdd (congrMonus h₁ h₂) (congrMonus h₂ h₁)

theorem two_le_dist_of_gap {x y : PTm n} (h : Γ ⊢[PRAAx] le (succ (succ x)) y) :
    Γ ⊢[PRAAx] le two (dist y x) := by
  have e : Γ ⊢[PRAAx] y ≐ x + (two + monus y (succ (succ x))) := by
    ipra_lc natEq (eq_add_of_le h)
  exact le_congr (.eqRefl _) (dist_of_add e).eqSymm (le_add_right _ _)

private theorem far_aux {a b M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hab : Γ ⊢[PRAAx] le a b)
    (hd : Γ ⊢[PRAAx] le (two * M) (monus b a)) :
    Γ ⊢[PRAAx] le (succ (succ (quo a M))) (quo b M) := by
  have hb : Γ ⊢[PRAAx] le (a + M + M) b := by
    refine le_of_eq_add (d := monus (monus b a) (two * M)) ?_
    ipra_lc natEq (eq_add_of_le hab) + natEq (eq_add_of_le hd)
  have e : Γ ⊢[PRAAx] quo (a + M + M) M ≐ succ (succ (quo a M)) :=
    (quo_add_self hM).eqTrans (congrSucc (quo_add_self hM))
  exact le_congr e (.eqRefl _) (quo_mono hM hb)

/-- `|a − b| ≥ 2M` gives `|⌊a/M⌋ − ⌊b/M⌋| ≥ 2`. -/
theorem quo_far {a b M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] le (two * M) (dist a b)) : Γ ⊢[PRAAx] le two (dist (quo a M) (quo b M)) := by
  refine .orE (le_total a b) ?_ ?_
  · have hd : (le a b :: Γ) ⊢[PRAAx] le (two * M) (monus b a) :=
      le_congr (.eqRefl _) ((congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (zero_add _)) h.wk
    exact le_congr (.eqRefl _) (dist_comm _ _) (two_le_dist_of_gap (far_aux hM.wk Prf.hyp0 hd))
  · have hd : (le b a :: Γ) ⊢[PRAAx] le (two * M) (monus a b) :=
      le_congr (.eqRefl _) ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _)) h.wk
    exact two_le_dist_of_gap (far_aux hM.wk Prf.hyp0 hd)

private theorem le_add_of_dist_lt {a b M : PTm n} (h : Γ ⊢[PRAAx] lt (dist a b) M) :
    Γ ⊢[PRAAx] le a (b + M) := by
  have h₁ : Γ ⊢[PRAAx] le a (monus a b + b) :=
    le_of_eq_add (d := monus b a) ((monus_max a b).eqTrans (add_comm _ _))
  have h₂ : Γ ⊢[PRAAx] le (monus a b) M := le_trans (le_add_right _ _) (le_of_lt h)
  exact le_congr (.eqRefl _) (add_comm _ _) (le_trans h₁ (add_le_add_right b h₂))

/-- `|a − b| < M` gives `⌊a/M⌋ ≤ ⌊b/M⌋ + 1` and `⌊b/M⌋ ≤ ⌊a/M⌋ + 1`. -/
theorem quo_near {a b M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] lt (dist a b) M) : Γ ⊢[PRAAx] near (quo a M) (quo b M) := by
  have h' : Γ ⊢[PRAAx] lt (dist b a) M := lt_congr (dist_comm a b) (.eqRefl _) h
  exact .andI (le_congr (.eqRefl _) (quo_add_self hM) (quo_mono hM (le_add_of_dist_lt h)))
    (le_congr (.eqRefl _) (quo_add_self hM) (quo_mono hM (le_add_of_dist_lt h')))

/-- `x ≤ y + 1` and `y ≤ x + 1` give `|x − y| ≤ 1`. -/
theorem dist_le_one_of_near {x y : PTm n} (h : Γ ⊢[PRAAx] near x y) :
    Γ ⊢[PRAAx] le (dist x y) one := by
  refine .orE (near_cases h) ?_ (.orE Prf.hyp0 ?_ ?_)
  · have e : ((x ≐ y) :: Γ) ⊢[PRAAx] x ≐ y + zero := Prf.hyp0.eqTrans (add_zero y).eqSymm
    exact le_congr (dist_of_add e).eqSymm (.eqRefl _) (zero_le one)
  · have e : ((y ≐ succ x) :: ((y ≐ succ x) ⋎ (x ≐ succ y)) :: Γ) ⊢[PRAAx] y ≐ x + one :=
      Prf.hyp0.eqTrans (succ_eq_add_one x)
    exact le_congr ((dist_comm x y).eqTrans (dist_of_add e)).eqSymm (.eqRefl _) (le_refl one)
  · have e : ((x ≐ succ y) :: ((y ≐ succ x) ⋎ (x ≐ succ y)) :: Γ) ⊢[PRAAx] x ≐ y + one :=
      Prf.hyp0.eqTrans (succ_eq_add_one y)
    exact le_congr (dist_of_add e).eqSymm (.eqRefl _) (le_refl one)

/-! ## The table in units of `M` -/

variable (F : PR 3)

/-- `⌊F(x, y, p) / M⌋` as a term in `x`, `y` and the packed parameter `⟨M, p⟩`. -/
def g3 : PTm 3 := quo (ap3 F (var 0) (var 1) (sndT (var 2))) (fstT (var 2))

/-- The table `(x, y, ⟨M, p⟩) ↦ ⌊F(x, y, p) / M⌋`. -/
def GF : PR 3 := PTm.toPR (g3 F)

theorem G_at (X Y q : PTm n) :
    Γ ⊢[PRAAx] ap3 (GF F) X Y q ≐ quo (ap3 F X Y (sndT q)) (fstT q) := by
  have h := toPR_eq (Γ := Γ) (g3 F) ![X, Y, q]
  have e : Syn.subst ![X, Y, q] (g3 F) = quo (ap3 F X Y (sndT q)) (fstT q) := by simp [g3]
  rw [e] at h
  exact h

theorem G_eq (X Y M p : PTm n) :
    Γ ⊢[PRAAx] ap3 (GF F) X Y (pairT M p) ≐ quo (ap3 F X Y p) M :=
  (G_at F X Y (pairT M p)).eqTrans
    (congrAp2 quoF (congrAp3 F (.eqRefl _) (.eqRefl _) (snd_pair M p)) (fst_pair M p))

section Pointwise

variable {X₁ Y₁ X₂ Y₂ M p : PTm n}

theorem G_far (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] le (two * M) (dist (ap3 F X₁ Y₁ p) (ap3 F X₂ Y₂ p))) :
    Γ ⊢[PRAAx] le two (dist (ap3 (GF F) X₁ Y₁ (pairT M p)) (ap3 (GF F) X₂ Y₂ (pairT M p))) :=
  le_congr (.eqRefl _) (dist_congr (G_eq F X₁ Y₁ M p) (G_eq F X₂ Y₂ M p)).eqSymm (quo_far hM h)

theorem G_close (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] lt (dist (ap3 F X₁ Y₁ p) (ap3 F X₂ Y₂ p)) M) :
    Γ ⊢[PRAAx] closeF (GF F) X₁ Y₁ X₂ Y₂ (pairT M p) :=
  le_congr (dist_congr (G_eq F X₁ Y₁ M p) (G_eq F X₂ Y₂ M p)).eqSymm (.eqRefl _)
    (dist_le_one_of_near (quo_near hM h))

end Pointwise

/-! ## The three conditions in the unit `M` -/

/-- `eq:sep`, first coordinate: `|F(0, y') − F(N, y)| ≥ 2M` for all `y, y' ≤ N`. -/
abbrev usep0F (N M p : PTm n) : Fm PTm n :=
  Fm.all (Fm.all (le (var 1) (Syn.shift (Syn.shift N)) ⟶ (le (var 0) (Syn.shift (Syn.shift N)) ⟶
    le (two * Syn.shift (Syn.shift M)) (dist (ap3 F zero (var 0) (Syn.shift (Syn.shift p)))
      (ap3 F (Syn.shift (Syn.shift N)) (var 1) (Syn.shift (Syn.shift p)))))))

/-- `eq:sep`, second coordinate: `|F(x', 0) − F(x, N)| ≥ 2M` for all `x, x' ≤ N`. -/
abbrev usep1F (N M p : PTm n) : Fm PTm n :=
  Fm.all (Fm.all (le (var 1) (Syn.shift (Syn.shift N)) ⟶ (le (var 0) (Syn.shift (Syn.shift N)) ⟶
    le (two * Syn.shift (Syn.shift M)) (dist (ap3 F (var 0) zero (Syn.shift (Syn.shift p)))
      (ap3 F (var 1) (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift p)))))))

/-- `|F(X₁, Y₁) − F(X₂, Y₂)| < M`. -/
abbrev nearF (X₁ Y₁ X₂ Y₂ M p : PTm n) : Fm PTm n :=
  lt (dist (ap3 F X₁ Y₁ p) (ap3 F X₂ Y₂ p)) M

/-- `eq:small`: for all `a, b < N`, the vertices of the two Kuhn triangles of the cell `(a, b)`
have values pairwise at distance `< M`. -/
abbrev usmallF (N M p : PTm n) : Fm PTm n :=
  Fm.all (Fm.all (lt (var 1) (Syn.shift (Syn.shift N)) ⟶ (lt (var 0) (Syn.shift (Syn.shift N)) ⟶
    (nearF F (var 1) (var 0) (succ (var 1)) (var 0) (Syn.shift (Syn.shift M))
        (Syn.shift (Syn.shift p)) ⋏
      (nearF F (succ (var 1)) (var 0) (succ (var 1)) (succ (var 0)) (Syn.shift (Syn.shift M))
          (Syn.shift (Syn.shift p)) ⋏
        (nearF F (var 1) (var 0) (succ (var 1)) (succ (var 0)) (Syn.shift (Syn.shift M))
            (Syn.shift (Syn.shift p)) ⋏
          (nearF F (var 1) (var 0) (var 1) (succ (var 0)) (Syn.shift (Syn.shift M))
              (Syn.shift (Syn.shift p)) ⋏
            nearF F (var 1) (succ (var 0)) (succ (var 1)) (succ (var 0)) (Syn.shift (Syn.shift M))
              (Syn.shift (Syn.shift p)))))))))

theorem shift_one : Syn.shift (one : PTm n) = one := by simp [Syn.shift]

theorem pos_shift2 {M : PTm n} (h : Γ ⊢[PRAAx] le one M) :
    (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      Syn.shift (Syn.shift M) ≐ succ (pred (Syn.shift (Syn.shift M))) := by
  have e := shift_le' (shift_le' h)
  rw [shift_one, shift_one] at e
  exact pos_succ e

variable {N M p : PTm n}

theorem sep0_units (hpos : Γ ⊢[PRAAx] le one M) (h : Γ ⊢[PRAAx] usep0F F N M p) :
    Γ ⊢[PRAAx] sep0F (GF F) N (pairT M p) := by
  refine .allI (.allI (.impI (.impI ?_)))
  rw [shift_pairT, shift_pairT]
  have hu := h.allOpen.allOpen
  exact G_far F (pos_shift2 hpos).wk.wk (.impE (.impE hu.wk.wk Prf.hyp1) Prf.hyp0)

theorem sep1_units (hpos : Γ ⊢[PRAAx] le one M) (h : Γ ⊢[PRAAx] usep1F F N M p) :
    Γ ⊢[PRAAx] sep1F (GF F) N (pairT M p) := by
  refine .allI (.allI (.impI (.impI ?_)))
  rw [shift_pairT, shift_pairT]
  have hu := h.allOpen.allOpen
  exact G_far F (pos_shift2 hpos).wk.wk (.impE (.impE hu.wk.wk Prf.hyp1) Prf.hyp0)

theorem small_units (hpos : Γ ⊢[PRAAx] le one M) (h : Γ ⊢[PRAAx] usmallF F N M p) :
    Γ ⊢[PRAAx] smallF (GF F) N (pairT M p) := by
  refine .allI (.allI (.impI (.impI ?_)))
  rw [shift_pairT, shift_pairT]
  have hu := h.allOpen.allOpen
  have h5 := Prf.impE (Prf.impE hu.wk.wk Prf.hyp1) Prf.hyp0
  exact .andI (G_close F (pos_shift2 hpos).wk.wk (.andE₁ h5))
    (.andI (G_close F (pos_shift2 hpos).wk.wk (.andE₁ (.andE₂ h5)))
      (.andI (G_close F (pos_shift2 hpos).wk.wk (.andE₁ (.andE₂ (.andE₂ h5))))
        (.andI (G_close F (pos_shift2 hpos).wk.wk (.andE₁ (.andE₂ (.andE₂ (.andE₂ h5)))))
          (G_close F (pos_shift2 hpos).wk.wk (.andE₂ (.andE₂ (.andE₂ (.andE₂ h5))))))))

/-- No natural-valued table on the grid `{0, …, N}²` has both pairs of opposite faces separated
by `2M` and all Kuhn triangles of diameter below `M`, for `M ≥ 1`. -/
theorem no_table_units (hpos : Γ ⊢[PRAAx] le one M) (h0 : Γ ⊢[PRAAx] usep0F F N M p)
    (h1 : Γ ⊢[PRAAx] usep1F F N M p) (hs : Γ ⊢[PRAAx] usmallF F N M p) : Γ ⊢[PRAAx] Fm.bot :=
  no_table (GF F) (sep0_units F hpos h0) (sep1_units F hpos h1) (small_units F hpos hs)

/-- Variables: `0 = N`, `1 = M`, `2 = p`. -/
abbrev unitsFormula : Fm PTm 3 :=
  le one (var 1) ⟶ usep0F F (var 0) (var 1) (var 2) ⟶ usep1F F (var 0) (var 1) (var 2) ⟶
    usmallF F (var 0) (var 1) (var 2) ⟶ Fm.bot

/-- `thm:finite` for `d = 2`, `m = 1` and `h = 2M`: for all `N`, `M ≥ 1` and `p`, the
separation `eq:sep` by `2M` and the strict small-simplex condition `eq:small` by `M` on the
table `F(·, ·, p)` are contradictory. -/
theorem no_table_units_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (unitsFormula F) :=
  closeUniv 3 (.impI (.impI (.impI (.impI
    (no_table_units F (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Topology.DimensionUnits
