import IPRADerivations.DiophantineNumberTheory.GaussLemma

/-!
# Eisenstein's lemma and the law of quadratic reciprocity

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`, `quadratic_reciprocity.tex`, `eq:eisenstein` and
`eq:qr`. The closed object sentence is `QuadraticReciprocityGoal.sentence`:

  for all `p`, `q`: if `p`, `q` are primes, both odd, and `p ≠ q`, then
  `par (signBit p q + signBit q p) = par (⌊p/2⌋ ⌊q/2⌋)`,

where `signBit p a` is the bit of the bounded formula "there is no `x < p` with `x² ≡ a (mod p)`"
(`Foundations/BoundedSyntax`). That is `(p/q)(q/p) = (−1)^{(p−1)(q−1)/4}`.

* `sign_eq`: `signBit p a = 1 − rb p a`, where `rb` is the residue bit of `GaussLemma` computed by the bounded
  search of `Foundations/BoundedReflection`: the two descriptions of "`a` is not a square modulo `p`" agree;
* `eisenstein_lemma`: `signBit p a = par (floorSum p a)` for an odd prime `p`, an odd `a` and `gcd(p, a) = 1`
  (`eq:eisenstein`), from Gauss's lemma (`GaussLemma.gauss_lemma`) and the parity conversion
  (`FoldedPermutation.floor_gauss_parity`);
* `quadratic_reciprocity`: the closed sentence, by `QuadraticReciprocityGoal.close_from_counts` with Eisenstein's
  lemma in both orientations and the lattice count `RectangleCount.rectangle_of_odd`.

The supplementary laws (`eq:minusone`, `eq:two`) and the square-root witness statements of the packet are not
derived.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.QuadraticReciprocity

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (not_dvd_prime)
open LeanProofs.IPRA.DiophantineNumberTheory.QuadraticReciprocityGoal (nonsquare signBit floorSum eisenstein
  rectangle assumptions sentence close_from_counts)
open LeanProofs.IPRA.DiophantineNumberTheory.RectangleCount (rectangle_of_odd)
open LeanProofs.IPRA.DiophantineNumberTheory.FoldedPermutation (floor_gauss_parity)
open LeanProofs.IPRA.DiophantineNumberTheory.PairProduct (sqB sq_search_witness sq_search_no_root)
open LeanProofs.IPRA.DiophantineNumberTheory.GaussLemma (rb gauss_lemma)
open LeanProofs.IPRA.Foundations.BoundedSyntax (formula bit bounded_reflection bit_zero_iff program_correct)
open LeanProofs.IPRA.Foundations.BoundedReflection (wit ex_cases)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The bounded formula and the search bit -/

/-- The matrix of the bounded existential: `x < p ∧ x² ≡ a (mod p)` over `0 = x`. -/
abbrev exF (p a : PTm n) : Fm PTm (n + 1) :=
  lt (var 0) (Syn.shift p) ⋏ (rem (var 0 * var 0) (Syn.shift p) ≐ rem (Syn.shift a) (Syn.shift p))

/-- The source formula of `signBit p a`. -/
theorem F_eq (p a : PTm n) : (formula nonsquare).subst ![p, a] = neg (Fm.ex (exF p a)) := by
  simp [formula, nonsquare, exF, Syn.shift, Syn.up]

theorem exF_at (p a w : PTm n) :
    (exF p a).subst (Syn.inst w) = (lt w p ⋏ (rem (w * w) p ≐ rem a p)) := by
  ipra_ind_simp [exF, subst_lt, subst_ap2, Syn.subst_inst_shift]

/-- No square root below `p`: the bounded formula holds. -/
theorem nr_formula {p a : PTm n} (hnr : Γ ⊢[PRAAx] rb p a ≐ zero) : Γ ⊢[PRAAx] neg (Fm.ex (exF p a)) := by
  refine .impI (Prf.exE Prf.hyp0 ?_)
  have hnr' : (Γ.map Fm.shift) ⊢[PRAAx] rb (Syn.shift p) (Syn.shift a) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using hnr.shift
  have h0 : (exF p a :: (Fm.ex (exF p a) :: Γ).map Fm.shift) ⊢[PRAAx] exF p a := Prf.hyp0
  exact .impE (sq_search_no_root hnr'.wk.wk (Prf.andE₁ h0)) (Prf.andE₂ h0)

/-- A square root below `p`: the bounded formula fails. -/
theorem res_formula {p a : PTm n} (hr : Γ ⊢[PRAAx] rb p a ≐ one) :
    Γ ⊢[PRAAx] neg (neg (Fm.ex (exF p a))) := by
  refine .impI (.impE Prf.hyp0 (Prf.exI (wit sqB p (pairT p a)) ?_))
  rw [exF_at]
  exact (sq_search_witness hr).wk

/-- `signBit p a = 1 − [∃ x < p, x² ≡ a (mod p)]`. -/
theorem sign_eq (p a : PTm n) : Γ ⊢[PRAAx] signBit p a ≐ monus one (rb p a) := by
  have pc : Γ ⊢[PRAAx] signBit p a ≐ bit nonsquare ![p, a] := program_correct nonsquare ![p, a]
  have br := bounded_reflection (Γ := Γ) nonsquare ![p, a]
  have bz := bit_zero_iff (Γ := Γ) nonsquare ![p, a]
  rw [F_eq] at br bz
  refine .orE (ex_cases sqB p (pairT p a)) ?_ ?_
  · have hnr : ((rb p a ≐ zero) :: Γ) ⊢[PRAAx] rb p a ≐ zero := Prf.hyp0
    have b1 := Prf.iffMpr br.wk (nr_formula hnr)
    exact pc.wk.eqTrans (b1.eqTrans ((congrMonus (.eqRefl _) hnr).eqTrans (monus_zero _)).eqSymm)
  · have hr : ((rb p a ≐ one) :: Γ) ⊢[PRAAx] rb p a ≐ one := Prf.hyp0
    have b0 := Prf.iffMpr bz.wk (res_formula hr)
    exact pc.wk.eqTrans (b0.eqTrans ((congrMonus (.eqRefl _) hr).eqTrans (monus_self _)).eqSymm)

/-! ## Eisenstein's lemma -/

/-- `eq:eisenstein`: `signBit p a = par (floorSum p a)` for an odd prime `p`, an odd `a` and `gcd(p, a) = 1`. -/
theorem eisenstein_lemma {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one)
    (ha : Γ ⊢[PRAAx] par a ≐ one) (hc : Γ ⊢[PRAAx] gcd p a ≐ one) : Γ ⊢[PRAAx] eisenstein p a := by
  have ha1 : Γ ⊢[PRAAx] a ≐ succ (pred a) :=
    pos_of_eq_succ (c := two * half a) ((odd_of ha).eqTrans (by ipra_ring))
  exact (sign_eq p a).eqTrans ((gauss_lemma hp hodd ha1 hc).eqSymm.eqTrans (floor_gauss_parity hodd ha hc).eqSymm)

/-! ## The law of quadratic reciprocity -/

/-- The hypotheses of the sentence give Eisenstein's lemma and the lattice count. -/
theorem premises {p q : PTm n} (h : Γ ⊢[PRAAx] assumptions p q) :
    (Γ ⊢[PRAAx] eisenstein p q) ∧ (Γ ⊢[PRAAx] eisenstein q p) ∧ (Γ ⊢[PRAAx] rectangle p q) := by
  have A : Γ ⊢[PRAAx] prime p ⋏ (prime q ⋏ ((par p ≐ one) ⋏ ((par q ≐ one) ⋏ neg (p ≐ q)))) := h
  have hp := Prf.andE₁ A
  have hq := Prf.andE₁ (Prf.andE₂ A)
  have op := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ A))
  have oq := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ A)))
  have ne := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ A)))
  have gpq : Γ ⊢[PRAAx] gcd p q ≐ one := gcd_prime hp (not_dvd_prime hp hq ne)
  have gqp : Γ ⊢[PRAAx] gcd q p ≐ one := gcd_prime hq (not_dvd_prime hq hp (Order.ne_symm ne))
  exact ⟨eisenstein_lemma hp op oq gpq, eisenstein_lemma hq oq op gqp, rectangle_of_odd op oq gpq⟩

/-- The law of quadratic reciprocity, as a closed sentence of iPRA: for distinct odd primes `p`, `q`,
`par (signBit p q + signBit q p) = par (⌊p/2⌋ ⌊q/2⌋)`. -/
theorem quadratic_reciprocity : ([] : List (Fm PTm 0)) ⊢[PRAAx] sentence := by
  obtain ⟨h1, h2, h3⟩ := premises (Γ := [assumptions (var 0 : PTm 2) (var 1)]) (p := var 0) (q := var 1) Prf.hyp0
  exact close_from_counts h1 h2 h3

end LeanProofs.IPRA.DiophantineNumberTheory.QuadraticReciprocity

export_ipra DiophantineNumberTheory.QuadraticReciprocity (sign_eq)
