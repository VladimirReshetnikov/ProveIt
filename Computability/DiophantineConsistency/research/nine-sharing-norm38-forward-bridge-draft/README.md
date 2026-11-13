# Uncompiled forward bridge for the 38-witness seed

`Norm38Forward.lean` proposes the missing direction from an original source
zero to a seed zero in a model of IΣ₁. Its final theorem takes an integer port
tuple `p`, model-natural representatives for all four ports, explicit cast
equalities, positive beta in the model difference ring, and a zero of the
14-variable source evaluated at `u+1`. It concludes a seed zero at input 1
with the 38-coordinate witness computed by `SharingForward38.witnessCoordinates`.

The source attempts three substantive intermediate steps:

1. The generated natural constructor preserves the 14-input prefix and
   satisfies all 60 static gate constraints. This part is formulated for any
   commutative semiring mapped to a commutative ring, without norm hypotheses.
2. The existing all-model five-norm theorem turns the positive source zero
   into P=Q=U=W=1 and strong=1. The drafted source-reference and topology
   proofs identify these with the static terminal values; the exact existing
   identity `Z = delta * strong` gives `Z=delta`. This direction uses the
   norm theorem's beta and coordinate positivity hypotheses explicitly.
3. Given static gate constraints and the five static norm targets, the 29
   indexed slot equalities yield all literal residual zeros; the separately
   drafted sum-of-squares equivalence then yields the seed zero.

**The file is an uncompiled draft, not an established model bridge.** The
29-slot identity and concrete reference/topology dependencies are uncompiled;
the first extraction attempt has already exposed finite-index simplification
errors and timed out. The generated `simp` proof of all 60 gates, dependent
list indexing, port casts, reference reduction, and final norm rewrites may
need substantial repair or splitting. The gate constructor and several seed
modules have separately compiled, but that does not prove the bridge here.

`generate.py` pins the reviewed slot table and emits the 19 gate hypotheses
and 29 slot arguments. `check.py` verifies these exact generated indices,
components and norm names, and reruns three separately reviewed external
source/graph checks. This is a source-binding check, not a Lean proof. Run
`python3 -I -S -B check.py`; no Lean process is used.

Actual fixed-current-port casts, both checked directions on a single provider
chain, Jones composition and the iPRA consistency endpoint remain separate.
The strong-factor identity needs no division; the source norm theorem still
requires its stated positivity and discrete model hypotheses.
