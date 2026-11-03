# Source review: model halt to a positive free-J zero, conditional on ports

This is an independent **source-only** review. I did not run Lean or audit
the complete provider closure. The final reviewed
`free-j-halt-model-zero-prototype/FreeJHaltModelZero.lean` has SHA-256
`74a760f5503e0845b7e34a38c458dc69d1f1d612f5c36ea24e18b054841e301f`.
I also inspected the immediate client source interfaces for the retained halt
witness, candidate valuation, auxiliary ordinate ordering, graph-rank
binding and final natural-data graph join. Their respective source hashes are
`0c928eee0eeee3edd0c3786cca902b08e69fdff3c84032e237b5cc4de307ef71`,
`ec11564650f612f6a20e8591ef4b9ec7ad4cddc332eb8ef48b7ea1c0eba3d3ca`,
`89ef868199f19ab6fc5d72d8ff00cafd587b2dd6fc4b0087410ac4f9737721d7`,
`8e99770d2e23e2d728c9f62c13e39629a542404ef450ce13649350c820ff26e2`, and
`f155601b5d8a8c9c6c5ead12e0e1c98edb915b16cb16ddcb24f861beb8df9694`.
The point-in-time namespaced rebuilt copies of the last two sources match
these two hashes. This inspection is not an independent authentication of
compiled objects or their full ancestry.

## Exact scope and assumptions

`halt_positive_zero_of_ports` quantifies over an arbitrary `ORingStructure`
model of `IΣ₁`, internal halting time `T`, and integer port tuple `p`. It
assumes the represented decimal215 halt and **four explicit model
interpretation equations**:

1. `ι(rep 590069 (haltLength T)) * (p 0 : DiffRing V) =
   ι(Exp.exp (590069 * haltLength T) - 1)`;
2. `(p 1 : DiffRing V) = ι(paramKernel rho : V)`;
3. `(p 2 : DiffRing V) = ι(low : V)`;
4. `(p 3 : DiffRing V) = ι(high + (Exp.exp 590069 - 1) : V)`.

The first is a repunit-scaled beta equation, rather than a literal statement
of a particular natural coefficient. The conclusion is existence of a
12-coordinate valuation `v`, all of whose entries are strictly positive,
with `InternalZero (Ordinary12FreeJ.literal p) v`. No hypotheses are added
for physical packing, rank calibration, Pell witnesses, positive transport,
adaptive gamma, auxiliary ordering, or the graph factor equations; those
are obtained from the imported source interfaces under the halt and port
assumptions.

## Witness and quantifier inspection

The proof first opens one `halt_first_gamma` result and its outer,
auxiliary, first-carrier and adaptive-gamma witnesses in the same scope. It
uses those very parameters for `CompactPositiveValuation.valuation`, with
slot 10 equal to `delta(a)*i+(y-auxw)` and slot 11 equal to the **adaptive**
gamma. It derives `auxw≤y` from the same auxiliary norm and positive seed
factors; thus natural subtraction can be used by the tail binding. The
separate transport power `w`, auxiliary `auxw`, seed `gammaOld`, adaptive
`gamma`, graph coordinate `f-1` and correction quotient `t` are consistently
distinguished. Positivity follows from the candidate valuation theorem;
all twelve coordinate equations supplied to the model-data join are `rfl`.

The rank-binding client uses precisely the selected word and the beta, low
and shifted-high port equations. The outer seed's `c=ycoord R a` supplies the
same graph `c=(eta+zeta)*Y+eta`. The final
`FreeJModelZeroJoin.zero_of_model_data` receives the same seed, transport,
gamma and auxiliary equations. Its stated conclusion is the actual free-J
literal's `InternalZero`, with no graph-zero assumption. No issue with
witness scope or the corrected ordinary-tail coordinate was found in the
source interfaces reviewed.

This conditional all-model theorem does **not** yet prove those four port
interpretation equations for the retained symbolic or displayed equation,
connect their symbolic tuple/bytes to the PDF, establish the other direction,
or show the existence of an iPRA derivation. The author's successful
single-side build, named axiom report and direct-guard observations are
separate from this review. Neither this review nor a source-hash match
establishes a paired replay or complete transitive, package and dynamic
provider provenance.
