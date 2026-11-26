import IPRADerivations.Core.ParityArith

/-!
# Two staggered grids of cells (`dimension_invariance_ipra`, `lem:cells` for two grids)

Packet: `topology/dimension_invariance_ipra`, Section "Staggered rational cells and the
dimension obstruction". For `d = 2` the two grids have cells of width `h` and are offset by
`h / 2`. Measured in units of `h / 2`, a sample is a natural number `g`, the cell of the first
grid is `half g = ⌊g / 2⌋` and the cell of the second grid is `half (g + 1) = ⌊(g + 1) / 2⌋`.
(The packet's second grid uses `⌊g / 2 − 1 / 2⌋`; the two differ by the constant `1`, so they
define the same partition, and this one stays in the natural numbers.)

For arbitrary terms, with `dist a b = (a ∸ b) + (b ∸ a)`:

* `cell0_ne_of_dist`, `cell1_ne_of_dist` (`lem:cells` (i), contrapositive): samples at
  distance at least `2`, that is at least `h`, lie in different cells of each grid;
* `near_of_dist`: samples at distance at most `1` satisfy `a ≤ b + 1` and `b ≤ a + 1`;
* `staggered` (`lem:cells` (ii), (iii) and the threshold argument, for two grids): if three
  samples `gu`, `gv`, `gw` are pairwise within `1`, that is within `h / 2`, then `gu`, `gw`
  share a cell of the first grid or `gv`, `gw` share a cell of the second grid. In the
  packet's terms: a threshold of the first grid between `gu` and `gw` and a threshold of the
  second grid between `gv` and `gw` would be at least `h / 2` apart, inside an interval
  shorter than `h / 2`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.StaggeredCells

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `|x − y|`. -/
abbrev dist (x y : PTm n) : PTm n := monus x y + monus y x

/-- `a ≤ b + 1` and `b ≤ a + 1`. -/
abbrev near (a b : PTm n) : Fm PTm n := le a (succ b) ⋏ le b (succ a)

/-! ## Samples at least `2` apart lie in different cells -/

private theorem gap_aux {a b ha hb pa pb c : PTm n} (ea : Γ ⊢[PRAAx] a ≐ two * ha + pa)
    (eb : Γ ⊢[PRAAx] b ≐ two * hb + pb) (eh : Γ ⊢[PRAAx] ha ≐ hb) (ep : Γ ⊢[PRAAx] pb ≐ c) :
    Γ ⊢[PRAAx] a + c ≐ b + pa := by
  ipra_lc natEq ea - natEq eb + 2 * natEq eh - natEq ep

/-- `a + 2 ≤ b` gives `⌊a / 2⌋ ≠ ⌊b / 2⌋`. -/
theorem half_ne_of_gap {a b : PTm n} (h : Γ ⊢[PRAAx] le (succ (succ a)) b) :
    Γ ⊢[PRAAx] neg (half a ≐ half b) := by
  refine .impI (.orE (par_cases b) ?_ ?_)
  · have e : ((par b ≐ zero) :: (half a ≐ half b) :: Γ) ⊢[PRAAx] a + zero ≐ b + par a :=
      gap_aux (half_par a) (half_par b) Prf.hyp1 Prf.hyp0
    have hba : ((par b ≐ zero) :: (half a ≐ half b) :: Γ) ⊢[PRAAx] le b a :=
      le_of_eq_add ((add_zero a).eqSymm.eqTrans e)
    exact not_succ_le_self a _ (le_trans (le_trans (le_succ_self (succ a)) h.wk.wk) hba)
  · have e : ((par b ≐ one) :: (half a ≐ half b) :: Γ) ⊢[PRAAx] a + one ≐ b + par a :=
      gap_aux (half_par a) (half_par b) Prf.hyp1 Prf.hyp0
    have hba : ((par b ≐ one) :: (half a ≐ half b) :: Γ) ⊢[PRAAx] le b (succ a) :=
      le_of_eq_add ((succ_eq_add_one a).eqTrans e)
    exact not_succ_le_self (succ a) _ (le_trans h.wk.wk hba)

private theorem le_succ2_of {a b m : PTm n} (hb : Γ ⊢[PRAAx] b ≐ a + m) (hm : Γ ⊢[PRAAx] le two m) :
    Γ ⊢[PRAAx] le (succ (succ a)) b := by
  have e₁ := natEq hb; have e₂ := natEq (eq_add_of_le hm)
  refine le_of_eq_add (d := monus m two) ?_
  ipra_lc e₁ + e₂

/-- `|a − b| ≥ 2` gives `a + 2 ≤ b` or `b + 2 ≤ a`. -/
theorem gap_of_dist {a b : PTm n} (h : Γ ⊢[PRAAx] le two (dist a b)) :
    Γ ⊢[PRAAx] le (succ (succ a)) b ⋎ le (succ (succ b)) a := by
  refine .orE (le_total a b) (.orI₁ ?_) (.orI₂ ?_)
  · have hd : (le a b :: Γ) ⊢[PRAAx] le two (monus b a) :=
      le_congr (.eqRefl _) ((congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (zero_add _)) h.wk
    exact le_succ2_of (eq_add_of_le Prf.hyp0) hd
  · have hd : (le b a :: Γ) ⊢[PRAAx] le two (monus a b) :=
      le_congr (.eqRefl _) ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _)) h.wk
    exact le_succ2_of (eq_add_of_le Prf.hyp0) hd

/-- Samples at distance at least `2` lie in different cells of the first grid. -/
theorem cell0_ne_of_dist {a b : PTm n} (h : Γ ⊢[PRAAx] le two (dist a b)) :
    Γ ⊢[PRAAx] neg (half a ≐ half b) := by
  refine .orE (gap_of_dist h) (half_ne_of_gap Prf.hyp0) (.impI ?_)
  have hn : ((half a ≐ half b) :: le (succ (succ b)) a :: Γ) ⊢[PRAAx] neg (half b ≐ half a) :=
    half_ne_of_gap Prf.hyp1
  exact .impE hn Prf.hyp0.eqSymm

theorem succ_le_succ {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (succ a) (succ b) :=
  (succ_monus_succ a b).eqTrans h

/-- Samples at distance at least `2` lie in different cells of the second grid. -/
theorem cell1_ne_of_dist {a b : PTm n} (h : Γ ⊢[PRAAx] le two (dist a b)) :
    Γ ⊢[PRAAx] neg (half (succ a) ≐ half (succ b)) := by
  refine .orE (gap_of_dist h) (half_ne_of_gap (succ_le_succ Prf.hyp0)) (.impI ?_)
  have hn : ((half (succ a) ≐ half (succ b)) :: le (succ (succ b)) a :: Γ) ⊢[PRAAx]
      neg (half (succ b) ≐ half (succ a)) := half_ne_of_gap (succ_le_succ Prf.hyp1)
  exact .impE hn Prf.hyp0.eqSymm

/-! ## Samples within `1` -/

private theorem le_succ_of_monus {a b : PTm n} (h : Γ ⊢[PRAAx] le (monus a b) one) :
    Γ ⊢[PRAAx] le a (succ b) := by
  have h₁ : Γ ⊢[PRAAx] le a (monus a b + b) :=
    le_of_eq_add (d := monus b a) ((monus_max a b).eqTrans (add_comm _ _))
  have h₂ : Γ ⊢[PRAAx] le (monus a b + b) (one + b) := add_le_add_right b h
  exact le_congr (.eqRefl _) ((succ_eq_add_one b).eqTrans (add_comm b one)).eqSymm (le_trans h₁ h₂)

/-- `|a − b| ≤ 1` gives `a ≤ b + 1` and `b ≤ a + 1`. -/
theorem near_of_dist {a b : PTm n} (h : Γ ⊢[PRAAx] le (dist a b) one) : Γ ⊢[PRAAx] near a b :=
  .andI (le_succ_of_monus (le_trans (le_add_right _ _) h))
    (le_succ_of_monus (le_trans (le_add_left _ _) h))

theorem near_symm {a b : PTm n} (h : Γ ⊢[PRAAx] near a b) : Γ ⊢[PRAAx] near b a :=
  .andI (.andE₂ h) (.andE₁ h)

/-- `a = b`, `b = a + 1` or `a = b + 1`. -/
theorem near_cases {a b : PTm n} (h : Γ ⊢[PRAAx] near a b) :
    Γ ⊢[PRAAx] (a ≐ b) ⋎ ((b ≐ succ a) ⋎ (a ≐ succ b)) := by
  refine .orE (lt_or_le a b) ?_ ?_
  · exact .orI₂ (.orI₁ (le_antisymm (.andE₂ h.wk) Prf.hyp0))
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · exact .orI₂ (.orI₂ (le_antisymm (.andE₁ h.wk.wk) Prf.hyp0))
    · exact .orI₁ Prf.hyp0.eqSymm

/-! ## The staggered grids -/

theorem half_succ_even {x : PTm n} (h : Γ ⊢[PRAAx] par x ≐ zero) :
    Γ ⊢[PRAAx] half (succ x) ≐ half x :=
  (half_succ x).eqTrans ((congrAdd (.eqRefl _) h).eqTrans (add_zero _))

theorem par_succ_odd {x : PTm n} (h : Γ ⊢[PRAAx] par x ≐ one) : Γ ⊢[PRAAx] par (succ x) ≐ zero :=
  (par_succ x).eqTrans ((congrMonus (.eqRefl _) h).eqTrans (monus_self _))

private theorem two_step_absurd {a c : PTm n} (φ : Fm PTm n) (h₁ : Γ ⊢[PRAAx] c ≐ succ (succ a))
    (h₂ : Γ ⊢[PRAAx] le c (succ a)) : Γ ⊢[PRAAx] φ :=
  not_succ_le_self (succ a) φ (le_congr h₁ (.eqRefl _) h₂)

private theorem case_below {gu gv gw : PTm n} (h₁ : Γ ⊢[PRAAx] gw ≐ succ gu)
    (h₂ : Γ ⊢[PRAAx] gw ≐ succ gv) :
    Γ ⊢[PRAAx] (half gu ≐ half gw) ⋎ (half (succ gv) ≐ half (succ gw)) := by
  refine .orE (par_cases gu) (.orI₁ ?_) (.orI₂ ?_)
  · exact ((congrAp1 halfF h₁.wk).eqTrans (half_succ_even Prf.hyp0)).eqSymm
  · have pw : ((par gu ≐ one) :: Γ) ⊢[PRAAx] par gw ≐ zero :=
      (congrAp1 parF h₁.wk).eqTrans (par_succ_odd Prf.hyp0)
    exact (congrAp1 halfF h₂.wk.eqSymm).eqTrans (half_succ_even pw).eqSymm

private theorem case_above {gu gv gw : PTm n} (h₁ : Γ ⊢[PRAAx] gu ≐ succ gw)
    (h₂ : Γ ⊢[PRAAx] gv ≐ succ gw) :
    Γ ⊢[PRAAx] (half gu ≐ half gw) ⋎ (half (succ gv) ≐ half (succ gw)) := by
  refine .orE (par_cases gw) (.orI₁ ?_) (.orI₂ ?_)
  · exact (congrAp1 halfF h₁.wk).eqTrans (half_succ_even Prf.hyp0)
  · exact (congrAp1 halfF (congrSucc h₂.wk)).eqTrans (half_succ_even (par_succ_odd Prf.hyp0))

/-- Three samples pairwise within `1`: `gu`, `gw` share a cell of the first grid, or `gv`, `gw`
share a cell of the second grid. -/
theorem staggered {gu gv gw : PTm n} (huw : Γ ⊢[PRAAx] near gu gw) (hvw : Γ ⊢[PRAAx] near gv gw)
    (huv : Γ ⊢[PRAAx] near gu gv) :
    Γ ⊢[PRAAx] (half gu ≐ half gw) ⋎ (half (succ gv) ≐ half (succ gw)) := by
  refine .orE (near_cases huw) (.orI₁ (congrAp1 halfF Prf.hyp0)) (.orE Prf.hyp0 ?_ ?_)
  · refine .orE (near_cases hvw.wk.wk) (.orI₂ (congrAp1 halfF (congrSucc Prf.hyp0)))
      (.orE Prf.hyp0 ?_ ?_)
    · exact case_below hyp2 Prf.hyp0
    · exact two_step_absurd _ (Prf.hyp0.eqTrans (congrSucc hyp2)) (.andE₂ huv.wk.wk.wk.wk)
  · refine .orE (near_cases hvw.wk.wk) (.orI₂ (congrAp1 halfF (congrSucc Prf.hyp0)))
      (.orE Prf.hyp0 ?_ ?_)
    · exact two_step_absurd _ (hyp2.eqTrans (congrSucc Prf.hyp0)) (.andE₁ huv.wk.wk.wk.wk)
    · exact case_above hyp2 Prf.hyp0

/-! ## Closed forms -/

/-- Variables: `0 = a`, `1 = b`. -/
abbrev separatedFormula : Fm PTm 2 :=
  le two (dist (var 0) (var 1)) ⟶
    (neg (half (var 0) ≐ half (var 1)) ⋏ neg (half (succ (var 0)) ≐ half (succ (var 1))))

/-- `lem:cells` (i), contrapositive: for all `a`, `b` with `|a − b| ≥ 2`, the cells of `a` and
`b` differ in both grids. -/
theorem separated_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 separatedFormula :=
  closeUniv 2 (.impI (.andI (cell0_ne_of_dist Prf.hyp0) (cell1_ne_of_dist Prf.hyp0)))

/-- Variables: `0 = gu`, `1 = gv`, `2 = gw`. -/
abbrev staggeredFormula : Fm PTm 3 :=
  le (dist (var 0) (var 2)) one ⟶ le (dist (var 1) (var 2)) one ⟶ le (dist (var 0) (var 1)) one ⟶
    ((half (var 0) ≐ half (var 2)) ⋎ (half (succ (var 1)) ≐ half (succ (var 2))))

/-- For all `gu`, `gv`, `gw` pairwise within `1`: `gu`, `gw` share a cell of the first grid or
`gv`, `gw` share a cell of the second grid. -/
theorem staggered_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 staggeredFormula :=
  closeUniv 3 (.impI (.impI (.impI
    (staggered (near_of_dist hyp2) (near_of_dist Prf.hyp1) (near_of_dist Prf.hyp0)))))

end LeanProofs.IPRA.Topology.StaggeredCells
