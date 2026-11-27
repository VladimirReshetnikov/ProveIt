import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.AnalyticNumberTheory.Valuation

/-!
# Finite reconstruction (`ipra_presentations_to_witnesses`, `prop:reconstruction`)

Packet: `foundations/ipra_presentations_to_witnesses`, proposition `prop:reconstruction`: for a
decidable validity predicate `V(p)`, a fixed PR observation `o(p)`, an explicitly computed finite
list `G` and a PR list producer `B(q)`, if (1) `V(p)` implies `o(p) ∈ G` and (2) for each
`q ∈ G` the list `B(q)` contains every valid `p` with `o(p) = q`, then the filtered union
`⋃_{q ∈ G} B(q)` "contains exactly the valid objects". Proof: "fix an arbitrary valid `p`. The
first premise supplies its observation among the finite `G`; the second supplies `p` in that
observation's list. Therefore `p` is visited and retained."

Data: unary terms `V` (validity bit), `o`, `g` (`G_i = g(i)`), `ℓ` (`|B(q)| = ℓ(q)`), a binary
term `b` (`B(q)_j = b(j, q)`), and a length `n` of `G`. Membership in a finite list is the
success bit `exB` of a bounded search (`Foundations/BoundedReflection`), and the positions are
primitive recursive terms:

* `I p`: the least `i < n` with `g(i) = o(p)`;
* `J p`: the least `j < ℓ(g(I p))` with `b(j, g(I p)) = p`;
* `reconstruct`: from the two premises at `p` (as object-level implications) and `V(p) = 1`:
  `I p < n`, `g(I p) = o(p)`, `J p < ℓ(g(I p))` and `b(J p, g(I p)) = p`. The valid object sits
  at the explicit position `(I p, J p)` of the union; `reconstruct_eq` is the last equation.

The other direction of "exactly the valid objects" is the filter test itself: an entry is kept
only if `V` holds of it. The removal of duplicates, with its prefix invariant, is not derived.
-/

namespace LeanProofs.IPRA.Foundations.FiniteReconstruction

open_ipra exports
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_elim)

variable {k : ℕ} {Γ : List (Fm PTm k)}

variable (o g ℓ : PTm 1) (b : PTm 2)

/-- The test `[g(i) = o(p)]`; variables `0 = i`, `1 = p`. -/
def iB : PTm 2 := eqb (inst1 g (var 0)) (inst1 o (var 1))

theorem inst2_iB (i p : PTm k) : inst2 (iB o g) i p = eqb (inst1 g i) (inst1 o p) := by
  show Syn.subst ![i, p] (iB o g) = _
  simp [iB]

/-- The test `[b(j, q) = p]`; variables `0 = j`, `1 = ⟨q, p⟩`. -/
def jB : PTm 2 := eqb (inst2 b (var 0) (fstT (var 1))) (sndT (var 1))

theorem jB_at (j q p : PTm k) :
    Γ ⊢[PRAAx] inst2 (jB b) j (pairT q p) ≐ eqb (inst2 b j q) p := by
  have e : inst2 (jB b) j (pairT q p) =
      eqb (inst2 b j (fstT (pairT q p))) (sndT (pairT q p)) := by
    show Syn.subst ![j, pairT q p] (jB b) = _
    simp [jB]
  rw [e]
  have h := Prf.eqCongr (Γ := Γ) (eqb (var 0) (var 1) : PTm 2)
    (σ := ![inst2 b j (fstT (pairT q p)), sndT (pairT q p)]) (σ' := ![inst2 b j q, p])
    (fun l => by
      fin_cases l
      · exact congrInst2 b (.eqRefl _) (fst_pair _ _)
      · exact snd_pair _ _)
  simpa using h

/-- The position of the observation of `p` in the grid. -/
abbrev I (n p : PTm k) : PTm k := wit (iB o g) n p

/-- The position of `p` in the list of its observation. -/
abbrev J (n p : PTm k) : PTm k :=
  wit (jB b) (inst1 ℓ (inst1 g (I o g n p))) (pairT (inst1 g (I o g n p)) p)

variable {o g ℓ b}

/-- `prop:reconstruction`, completeness: a valid object is at the position `(I p, J p)` of the
union of the lists. The two hypotheses are the premises of the proposition at `p`: (1) a valid
`p` has its observation in the grid, and (2) a valid `p` whose observation is the grid entry
found lies in that entry's list. -/
theorem reconstruct {V : PTm 1} {n p : PTm k}
    (h₁ : Γ ⊢[PRAAx] (inst1 V p ≐ one) ⟶ (exB (iB o g) n p ≐ one))
    (h₂ : Γ ⊢[PRAAx] (inst1 V p ≐ one) ⟶ (inst1 g (I o g n p) ≐ inst1 o p) ⟶
      (exB (jB b) (inst1 ℓ (inst1 g (I o g n p))) (pairT (inst1 g (I o g n p)) p) ≐ one))
    (hV : Γ ⊢[PRAAx] inst1 V p ≐ one) :
    Γ ⊢[PRAAx] lt (I o g n p) n ⋏ ((inst1 g (I o g n p) ≐ inst1 o p) ⋏
      (lt (J o g ℓ b n p) (inst1 ℓ (inst1 g (I o g n p))) ⋏
        (inst2 b (J o g ℓ b n p) (inst1 g (I o g n p)) ≐ p))) := by
  have a := ex_elim (iB o g) (.impE h₁ hV)
  have a₂ := Prf.andE₂ a
  rw [inst2_iB] at a₂
  have hg := eq_of_eqb_ne a₂
  have c := ex_elim (jB b) (.impE (.impE h₂ hV) hg)
  have hb : Γ ⊢[PRAAx] inst2 b (J o g ℓ b n p) (inst1 g (I o g n p)) ≐ p :=
    eq_of_eqb_ne (.impI (.impE (Prf.andE₂ c).wk ((jB_at b _ _ _).eqTrans Prf.hyp0)))
  exact .andI (Prf.andE₁ a) (.andI hg (.andI (Prf.andE₁ c) hb))

/-- The valid object is recovered from its position, as one equation: `b(J p, g(I p)) = p`. -/
theorem reconstruct_eq {V : PTm 1} {n p : PTm k}
    (h₁ : Γ ⊢[PRAAx] (inst1 V p ≐ one) ⟶ (exB (iB o g) n p ≐ one))
    (h₂ : Γ ⊢[PRAAx] (inst1 V p ≐ one) ⟶ (inst1 g (I o g n p) ≐ inst1 o p) ⟶
      (exB (jB b) (inst1 ℓ (inst1 g (I o g n p))) (pairT (inst1 g (I o g n p)) p) ≐ one))
    (hV : Γ ⊢[PRAAx] inst1 V p ≐ one) :
    Γ ⊢[PRAAx] inst2 b (J o g ℓ b n p) (inst1 g (I o g n p)) ≐ p :=
  Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (reconstruct h₁ h₂ hV)))

end LeanProofs.IPRA.Foundations.FiniteReconstruction
