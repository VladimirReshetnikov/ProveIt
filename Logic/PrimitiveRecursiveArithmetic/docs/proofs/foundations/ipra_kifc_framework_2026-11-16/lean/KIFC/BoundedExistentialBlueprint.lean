import KIFC.SearchBlueprint

/-!
# Bounded existential normal form

This file states the proof-producing interface corresponding to
Theorem `bounded-ex-normal` in the report.  Every bounded existential is
compiled to a total least-witness term, a found flag, and a quantifier-free
certificate matrix.  The actual search proof is inherited from
`IPRADerivations.Core.Search` through `KIFC.SearchBlueprint`.
-/

namespace LeanProofs.KIFC

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-- Kernel-facing result of compiling one fixed bounded existential formula. -/
structure BoundedExistsCertificate (n : ℕ) where
  /-- The original bounded existential, with all binders already generated. -/
  existsFormula : Fm PTm n
  /-- Total primitive-recursive found flag. -/
  found : PTm n
  /-- Total primitive-recursive least-witness term. -/
  witness : PTm n
  /-- Quantifier-free matrix recording foundness, bound, validity, and leastness. -/
  leastCertificate : Fm PTm n
  leastCertificateQF : leastCertificate.QF
  existsIffFound : ([] : List (Fm PTm n)) ⊢[PRAAx]
    Fm.iff existsFormula (found ≐ one)
  foundIffCertificate : ([] : List (Fm PTm n)) ⊢[PRAAx]
    Fm.iff (found ≐ one) leastCertificate

namespace BoundedExistsCertificate

/-- A consumer may replace the bounded existential by the generated QF
certificate through two cuts.  The implementation is ordinary implication
composition from the two `Fm.iff` fields. -/
structure ConsumerTarget {n : ℕ} (c : BoundedExistsCertificate n) where
  conclusion : Fm PTm n
  fromCertificate : [c.leastCertificate] ⊢[PRAAx] conclusion

end BoundedExistsCertificate

/-!
Implementation checklist:

* generate the bounded formula and its `Reflected` Boolean code;
* adapt the code with `zeroOnTrue` and instantiate checked `Search.mu`;
* build the leastness prefix as a bounded all-fold equation;
* prove `leastCertificate.QF` by syntax recursion;
* compose `search_found`, `search_spec`, `search_minimal`, and fold reflection;
* expose a theorem under any precondition `H` by implication introduction and
  substitution of the total witness term.
-/

end LeanProofs.KIFC
