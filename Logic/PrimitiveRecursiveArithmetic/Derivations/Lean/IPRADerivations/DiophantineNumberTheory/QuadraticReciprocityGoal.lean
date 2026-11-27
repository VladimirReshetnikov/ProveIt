import IPRADerivations.AnalyticNumberTheory.Primes
import IPRADerivations.Core.ParityArith
import IPRADerivations.Foundations.BoundedSyntax

/-!
# Quadratic reciprocity: the object sentence and its assembly from the two counts

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`, `quadratic_reciprocity.tex` (Sections 7 to 9) and
`repo/Goal.lean` (the packet's object-language file, adapted here and compiled against this workspace).

* `nonsquare`, `signBit`: the bounded formula "no `x < p` has `x² ≡ a (mod p)`" and its primitive recursive bit
  (`Foundations/BoundedSyntax`), with `nonsquare_reflection`: the bit is `1` exactly when the formula holds;
* `floorSum p a = Σ_{i < ⌊p/2⌋} ⌊(i + 1) a / p⌋`;
* `sentence`: for distinct odd primes `p`, `q`, the parity of `signBit p q + signBit q p` is the parity of
  `⌊p/2⌋ ⌊q/2⌋`, the product law for the Legendre symbols written with sign bits;
* `eisenstein p a`: `signBit p a = par (floorSum p a)` (Eisenstein's lemma), and `rectangle p q`:
  `floorSum p q + floorSum q p = ⌊p/2⌋ ⌊q/2⌋` (the lattice count);
* `assemble`, `close_from_counts`: the sentence follows from Eisenstein's lemma in both orientations and the
  rectangle count, by `par_add`.

Eisenstein's lemma and the rectangle count are hypotheses here; they, the supplementary laws and the square-root
witness statements of the packet are not derived.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.QuadraticReciprocityGoal
open_ipra exports
open LeanProofs.IPRA.Foundations.BoundedSyntax

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Outer variables are `0 = p, 1 = a`. Under the binder they become
`0 = x, 1 = p, 2 = a`. Negation is constructive since the search is bounded. -/
def nonsquare : BFm 2 :=
  .not (.ex (var 0) (.eq (rem (var 0 * var 0) (var 1)) (rem (var 2) (var 1))))

/-- The symbol is a sign bit on nonzero residue classes: 1 means a nonsquare. -/
def signBit (p a : PTm n) : PTm n := app (bitF nonsquare) ![p, a]

/-- Reuse the internal Boolean compiler's closed correctness proof. -/
theorem nonsquare_reflection :
    ([] : List (Fm PTm 0)) ⊢[PRAAx]
      univ 2 (Fm.iff (app (bitF nonsquare) var ≐ one) (formula nonsquare)) :=
  boolean_reflection_closed nonsquare

/-- Sum over 0 ≤ i < half(p) of floor((i + 1) * a / p). -/
def floorSum (p a : PTm n) : PTm n :=
  ap3 (sum2F (quo (succ (var 0) * var 2) (var 1))) (half p) p a

def assumptions (p q : PTm n) : Fm PTm n :=
  prime p ⋏ (prime q ⋏ ((par p ≐ one) ⋏ ((par q ≐ one) ⋏ neg (p ≐ q))))

def conclusion (p q : PTm n) : Fm PTm n :=
  par (signBit p q + signBit q p) ≐ par (half p * half q)

/-- The theorem to be derived in iPRA. -/
def sentence : Fm PTm 0 :=
  univ 2 (assumptions (var 0) (var 1) ⟶ conclusion (var 0) (var 1))

/-- Eisenstein's lemma for these two arguments. -/
def eisenstein (p a : PTm n) : Fm PTm n :=
  signBit p a ≐ par (floorSum p a)

/-- Exact lattice count, before taking parities. -/
def rectangle (p q : PTm n) : Fm PTm n :=
  floorSum p q + floorSum q p ≐ half p * half q

/-- This proves the final step directly in the object logic, in any context.
The manuscript supplies the argument for each premise. -/
theorem assemble (p q : PTm n)
    (hp : Γ ⊢[PRAAx] eisenstein p q) (hq : Γ ⊢[PRAAx] eisenstein q p)
    (hr : Γ ⊢[PRAAx] rectangle p q) : Γ ⊢[PRAAx] conclusion p q := by
  change Γ ⊢[PRAAx] signBit p q ≐ par (floorSum p q) at hp
  change Γ ⊢[PRAAx] signBit q p ≐ par (floorSum q p) at hq
  change Γ ⊢[PRAAx] floorSum p q + floorSum q p ≐ half p * half q at hr
  exact ((congrAp1 parF (congrAdd hp hq)).eqTrans
    (par_add (floorSum p q) (floorSum q p)).eqSymm).eqTrans (congrAp1 parF hr)

private abbrev P : PTm 2 := var 0
private abbrev Q : PTm 2 := var 1

/-- Closing the hypotheses and both number variables produces the requested
object sentence. Each input is a proof in the one-assumption object context. -/
theorem close_from_counts
    (hp : [assumptions P Q] ⊢[PRAAx] eisenstein P Q)
    (hq : [assumptions P Q] ⊢[PRAAx] eisenstein Q P)
    (hr : [assumptions P Q] ⊢[PRAAx] rectangle P Q) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] sentence := by
  exact closeUniv 2 (Prf.impI (assemble P Q hp hq hr))

end LeanProofs.IPRA.DiophantineNumberTheory.QuadraticReciprocityGoal

export_ipra DiophantineNumberTheory.QuadraticReciprocityGoal (floorSum signBit)
