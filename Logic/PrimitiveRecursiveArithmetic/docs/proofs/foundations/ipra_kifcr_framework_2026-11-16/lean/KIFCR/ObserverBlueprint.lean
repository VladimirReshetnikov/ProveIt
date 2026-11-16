import KIFCR.RelationalBlueprint
import IPRADerivations.Core.Integers
import IPRADerivations.Core.SumLemmas

/-!
# Stable observers and quantitative names blueprint

Exact observer independence erases finite witness choice.  Metric observers
require explicit rational diameter bounds.  A coherent infinite name requires
an additional adjacent-motion budget and a primitive-recursive tail modulus.
-/

namespace LeanProofs.KIFCR

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-- Contract of a generated finite tail estimate. -/
structure TailCertificate (n : ℕ) where
  pre : Fm PTm n
  start : PTm n
  finish : PTm n
  finiteSum : PTm n
  requestedBound : Fm PTm n
  sound : [pre] ⊢[PRAAx] requestedBound

/-!
Formalization order:

* exact observer theorem with two explicit candidate terms;
* least-selected candidate obtained from checked search;
* signed rational metric and triangle inequality;
* diameter observer theorem;
* finite telescoping sum using checked sum lemmas;
* regular-name theorem parameterized by an explicit tail-modulus term;
* gap-guarded collapse from relation/cluster output to one exact label.

Do not derive a modulus from metastability or from pointwise diameter shrinking.
-/

end LeanProofs.KIFCR
