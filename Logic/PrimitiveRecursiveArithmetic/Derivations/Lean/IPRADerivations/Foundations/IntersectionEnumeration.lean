import IPRADerivations.Foundations.RationalRootScan
import IPRADerivations.Probability.UnionUtility
import IPRADerivations.Core.Header

/-!
# The two-level intersection scan and global covers (`ipra_presentations_to_witnesses`, `thm:norm-complete-intersection`, `cor:norm-global-list`)

Packet: `foundations/ipra_presentations_to_witnesses`, theorem `thm:norm-complete-intersection`:
with `A = Roots_ℚ(N_G)` and `B_a = Roots_ℚ(F_a)`, "the output list is
`I(F, G) = [(a, b) : a ∈ A, b ∈ B_a, G(a, b) = 0]` (NI) ... An explicit primitive recursive height
bound is `H(F, G) = max({1, B(N_G)} ∪ {B(F_a) : a ∈ A})` (NH) ... Every common rational zero has
height at most `H(F, G)`." Proof: "If a pair is output, its first coordinate is in `A`, its
second coordinate is an exact root of `F_a`, and the final test gives `G(a, b) = 0` ...
Conversely ... completeness of the first root scan puts `a` in `A`. Since `F_a(b) = 0`,
completeness of the second scan puts `b` in `B_a`. The final test passes ... After this finite
list is computed, the maximum of its specialized bounds is another primitive recursive fold."
And corollary `cor:norm-global-list`: under a supplied global cover
`F(a, b) = 0 ∧ S(a, b) ⟹ ⋁_j G_j(a, b) = 0`, "concatenate the lists `I(F, G_j)` ... The maximum of
the bounds `H(F, G_j)`, or one for an empty cover, is a height bound ... This is a finite
intuitionistic disjunction elimination".

The two scans are those of `Foundations/RationalRootScan` (rank/select lists over pair codes).
The tests are parameters: `K₁(c, y)` retains first-coordinate codes, `K₂(c', ⟨c, y⟩)` retains
second-coordinate codes for the first coordinate `c` (the root test for `F_a` conjoined with the
final test `G(a, b) = 0`); `V(r, y)` is the radius of the second scan for the `r`-th
first-coordinate candidate (the packet's `B(F_a)`), and `Mx V ℓ y = max_{r<ℓ} V(r, y)` is the
bounded maximum of `Probability/UnionUtility`:

* `cand`, `par`, `height`: the `r`-th candidate, the parameter of its second scan, and (NH);
* `neg_congr`: a negated equation transported along an equation of terms;
* `inter_sound`: a listed pair passes both tests;
* `inter_complete`: a pair passing both tests, with first entries at most `B₁` and second
  entries at most the radius of its block, is listed: in block `r = rank K₁ c` at position
  `rank K₂ c' ⟨cand r, y⟩`;
* `inter_height`: all four entries of such a pair are at most `H = max{1, B₁, max_r V(r)}`.

Absence of repetitions is `scan_nodup` twice: equal first codes give equal block indices, and
within a block equal second codes give equal positions.

Global covers, for every number `m` of sections (a parameter of the Lean statements):

* `disjFin`, `disjFin_intro`, `disjFin_imp`: finite disjunctions (`⊥` when `m = 0`);
* `global_cover`: from a derivation of the cover `⋁_j φ_j` and derivations `φ_j ⊢ ψ_j`
  (membership in the `j`-th list), a derivation of `⋁_j ψ_j`;
* `maxFin`, `le_maxFin`, `global_height`: the maximum of the bounds (`1` for an empty cover)
  bounds whatever one of them bounds.

Not derived: the tests as programs on coefficient codes (specialization `F_a`, evaluation of
`G`), the concatenation of the `m` lists into one list term with the removal of duplicates
(`Foundations/Deduplication` treats one list), and the retention of the pairs satisfying `S`.
-/

namespace LeanProofs.IPRA.Foundations.IntersectionEnumeration

open_ipra
open LeanProofs.IPRA.Foundations.RationalRootScan
  (mx le_mx_left le_mx_right box scan_sound scan_complete)
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel)
open LeanProofs.IPRA.Probability.UnionUtility (Mx mx_upper)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## The two-level scan -/

section Scan

variable (K₁ K₂ V : PTm 2)

/-- The code of the `r`-th first-coordinate candidate. -/
abbrev cand (r B₁ y : PTm k) : PTm k := sel K₁ r (box B₁) y

/-- The parameter of the second scan in the block of the `r`-th candidate. -/
abbrev par (r B₁ y : PTm k) : PTm k := pairT (cand K₁ r B₁ y) y

/-- (NH): `H = max{1, B₁, max_{r<ℓ} V(r, y)}`, with `ℓ` the number of candidates. -/
abbrev height (B₁ y : PTm k) : PTm k := mx one (mx B₁ (Mx V (rank K₁ (box B₁) y) y))

/-- A negated equation, transported along an equation of terms. -/
theorem neg_congr {s t : PTm k} (e : Γ ⊢[PRAAx] s ≐ t) (h : Γ ⊢[PRAAx] neg (s ≐ zero)) :
    Γ ⊢[PRAAx] neg (t ≐ zero) :=
  .impI (.impE h.wk (e.wk.eqTrans Prf.hyp0))

/-- Soundness: a listed pair passes the first test and, in its block, the second test. -/
theorem inter_sound {r j B₁ y : PTm k} (hr : Γ ⊢[PRAAx] lt r (rank K₁ (box B₁) y))
    (hj : Γ ⊢[PRAAx] lt j (rank K₂ (box (inst2 V r y)) (par K₁ r B₁ y))) :
    Γ ⊢[PRAAx] neg (inst2 K₁ (cand K₁ r B₁ y) y ≐ zero) ⋏
      neg (inst2 K₂ (sel K₂ j (box (inst2 V r y)) (par K₁ r B₁ y)) (par K₁ r B₁ y) ≐ zero) :=
  .andI (Prf.andE₂ (scan_sound K₁ hr)) (Prf.andE₂ (scan_sound K₂ hj))

/-- Completeness: a pair of codes passing both tests, within the two radii, is listed. -/
theorem inter_complete {p₁ q₁ p₂ q₂ B₁ y : PTm k}
    (h₁p : Γ ⊢[PRAAx] le p₁ B₁) (h₁q : Γ ⊢[PRAAx] le q₁ B₁)
    (hk₁ : Γ ⊢[PRAAx] neg (inst2 K₁ (pairT p₁ q₁) y ≐ zero))
    (h₂p : Γ ⊢[PRAAx] le p₂ (inst2 V (rank K₁ (pairT p₁ q₁) y) y))
    (h₂q : Γ ⊢[PRAAx] le q₂ (inst2 V (rank K₁ (pairT p₁ q₁) y) y))
    (hk₂ : Γ ⊢[PRAAx] neg (inst2 K₂ (pairT p₂ q₂) (pairT (pairT p₁ q₁) y) ≐ zero)) :
    Γ ⊢[PRAAx]
      (lt (rank K₁ (pairT p₁ q₁) y) (rank K₁ (box B₁) y) ⋏
        (cand K₁ (rank K₁ (pairT p₁ q₁) y) B₁ y ≐ pairT p₁ q₁)) ⋏
      (lt (rank K₂ (pairT p₂ q₂) (par K₁ (rank K₁ (pairT p₁ q₁) y) B₁ y))
          (rank K₂ (box (inst2 V (rank K₁ (pairT p₁ q₁) y) y))
            (par K₁ (rank K₁ (pairT p₁ q₁) y) B₁ y)) ⋏
        (sel K₂ (rank K₂ (pairT p₂ q₂) (par K₁ (rank K₁ (pairT p₁ q₁) y) B₁ y))
            (box (inst2 V (rank K₁ (pairT p₁ q₁) y) y))
            (par K₁ (rank K₁ (pairT p₁ q₁) y) B₁ y) ≐ pairT p₂ q₂)) := by
  have c₁ := scan_complete K₁ h₁p h₁q hk₁
  have e : Γ ⊢[PRAAx] pairT (pairT p₁ q₁) y ≐ par K₁ (rank K₁ (pairT p₁ q₁) y) B₁ y := by
    have ec := (Prf.andE₂ c₁).eqSymm
    exact congrAdd (congrMul (congrAdd ec (.eqRefl y)) (congrAdd ec (.eqRefl y))) ec
  have hk₂' := neg_congr (congrInst2 K₂ (.eqRefl (pairT p₂ q₂)) e) hk₂
  exact .andI c₁ (scan_complete K₂ h₂p h₂q hk₂')

/-- (NH): every entry of a common zero is at most `H`. -/
theorem inter_height {p₁ q₁ p₂ q₂ B₁ y : PTm k}
    (h₁p : Γ ⊢[PRAAx] le p₁ B₁) (h₁q : Γ ⊢[PRAAx] le q₁ B₁)
    (hk₁ : Γ ⊢[PRAAx] neg (inst2 K₁ (pairT p₁ q₁) y ≐ zero))
    (h₂p : Γ ⊢[PRAAx] le p₂ (inst2 V (rank K₁ (pairT p₁ q₁) y) y))
    (h₂q : Γ ⊢[PRAAx] le q₂ (inst2 V (rank K₁ (pairT p₁ q₁) y) y)) :
    Γ ⊢[PRAAx] (le p₁ (height K₁ V B₁ y) ⋏ le q₁ (height K₁ V B₁ y)) ⋏
      (le p₂ (height K₁ V B₁ y) ⋏ le q₂ (height K₁ V B₁ y)) := by
  have hr := Prf.andE₁ (scan_complete K₁ h₁p h₁q hk₁)
  have hV : Γ ⊢[PRAAx] le (inst2 V (rank K₁ (pairT p₁ q₁) y) y) (height K₁ V B₁ y) :=
    le_trans (mx_upper V hr) (le_trans (le_mx_right _ _) (le_mx_right _ _))
  have hB : Γ ⊢[PRAAx] le B₁ (height K₁ V B₁ y) :=
    le_trans (le_mx_left _ _) (le_mx_right _ _)
  exact .andI (.andI (le_trans h₁p hB) (le_trans h₁q hB))
    (.andI (le_trans h₂p hV) (le_trans h₂q hV))

end Scan

/-! ## Global covers -/

/-- A finite disjunction; `⊥` for the empty family. -/
def disjFin : {m : ℕ} → (Fin m → Fm PTm k) → Fm PTm k
  | 0, _ => Fm.bot
  | 1, f => f 0
  | _ + 2, f => f 0 ⋎ disjFin fun i => f i.succ

theorem disjFin_intro : {m : ℕ} → {f : Fin m → Fm PTm k} → (i : Fin m) → (Γ ⊢[PRAAx] f i) →
    (Γ ⊢[PRAAx] disjFin f)
  | 0, _, i, _ => i.elim0
  | 1, f, i, h => by
    have e : i = 0 := Subsingleton.elim _ _
    subst e
    exact h
  | _ + 2, f, i, h => by
    revert h
    refine Fin.cases (fun h => ?_) (fun j h => ?_) i
    · exact .orI₁ h
    · exact .orI₂ (disjFin_intro j h)

theorem disjFin_imp : {m : ℕ} → {f : Fin m → Fm PTm k} → {χ : Fm PTm k} →
    (∀ i, Γ ⊢[PRAAx] f i ⟶ χ) → (Γ ⊢[PRAAx] disjFin f ⟶ χ)
  | 0, _, χ, _ => .impI (.botE χ Prf.hyp0)
  | 1, _, _, g => g 0
  | _ + 2, _, _, g =>
    .impI (.orE Prf.hyp0 (.impE (g 0).wk.wk Prf.hyp0)
      (.impE (disjFin_imp fun i => g i.succ).wk.wk Prf.hyp0))

/-- `cor:norm-global-list`: a supplied cover and membership in each section's list give
membership in one of the lists. For the empty cover the hypothesis is `⊥`. -/
theorem global_cover {m : ℕ} {φ ψ : Fin m → Fm PTm k} (hc : Γ ⊢[PRAAx] disjFin φ)
    (h : ∀ j, (φ j :: Γ) ⊢[PRAAx] ψ j) : Γ ⊢[PRAAx] disjFin ψ :=
  .impE (disjFin_imp fun j => .impI (disjFin_intro j (h j))) hc

/-- "The maximum of the bounds `H(F, G_j)`, or one for an empty cover". -/
def maxFin : {m : ℕ} → (Fin m → PTm k) → PTm k
  | 0, _ => one
  | _ + 1, H => mx (H 0) (maxFin fun i => H i.succ)

theorem le_maxFin : {m : ℕ} → (H : Fin m → PTm k) → (i : Fin m) →
    (Γ ⊢[PRAAx] le (H i) (maxFin H))
  | 0, _, i => i.elim0
  | _ + 1, H, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_mx_left _ _
    · exact le_trans (le_maxFin (fun i => H i.succ) j) (le_mx_right _ _)

/-- A quantity bounded by one of the section bounds is bounded by their maximum. -/
theorem global_height {m : ℕ} {H : Fin m → PTm k} {t : PTm k}
    (h : Γ ⊢[PRAAx] disjFin fun j => le t (H j)) : Γ ⊢[PRAAx] le t (maxFin H) :=
  .impE (disjFin_imp fun j => .impI (le_trans Prf.hyp0 (le_maxFin H j))) h

end LeanProofs.IPRA.Foundations.IntersectionEnumeration
