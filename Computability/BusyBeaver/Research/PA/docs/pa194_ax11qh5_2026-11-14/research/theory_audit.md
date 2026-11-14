# Logical and architectural audit

Snapshot: ProveIt `4be5c6e3a10292a7466f5d3687e3b39615ff049b`.

## Proof strength of the inherited result

`Computability/BusyBeaver/Research/PA/README.md` carefully distinguishes ordinary
mathematical PA-calibration arguments from the in-progress Lean/iPRA endpoint.
The primary PA194 packet's `report/calibration.tex` gives an ordinary syntactic
argument for `PA |- Halt(PA194) <-> exists p Prf_PA(p,0=1)`. Its dependency chain
uses a calibrated finite-set numerical calculus, a strong all-store command-word
compiler, exhaustive command scheduling, and positive finite physical simulation.
The maintained README says the end-to-end machine-specific iPRA reductions are
still open. Standard finite-run Lean results or Python symbolic certificates do
not turn those open obligations into completed Lean theorems.

The soundness argument is syntactic, not an appeal to PA's truth: each source
formula in the store has an explicit PA proof of its arithmetic translation;
primitive recursive transformations update those proof annotations. A halt
therefore produces a PA refutation. Conversely a source refutation is compiled
to a word that halts from *every* incoming store, essential because the scheduler
retains stores between trials.

## Rejected easy logical simplifications

### Universal elimination cannot replace the first head

The first head is

`O(d,H) = (U(d,U(d,H) -> 1) -> 1) -> H`.

This carries modal symmetry as well as explosion. Replacing it with
`U(d,H) -> H` supplies modal reflexivity but loses the symmetry used in the
vacuity-through-negation argument. The corpus contains both this warning and
countermodels; see `pa194q_conpa_2026-11-13/report/pa194q_report.tex` and
`pa_consistency_comparison_2026_11_13/sections/logic.tex`.

### Contraposition has a bootstrap condition

Let `X=U(d,U(d,H)->1)`. The exact known split is

`B(d,H)=(H->1)->X`, together with `E(A)=1->A`.

The old head and the split derive the same formulas via finite positive
implicational templates. The second component is essential. With material
implication, every membership atom true, every equality atom false, and every
quantifier the identity, all retained heads, gates and either usual dual-B
presentation hold, but `1->3` fails. Thus dual-B alone is not a sound replacement
for the *syntactic role* of the old head, despite equivalence in ordinary
classical first-order semantics with genuine falsity.

The existing `pa_consistency_comparison_2026_11_13` packet supplies 77-node Hilbert
proof DAGs for the two split translations and a 17-node explosion template.
These are prior art in this corpus.

### Conditional equality witness needs a new calibration

The proposed shorter head

`W*(d,H)=U(d,E(H,d)->1)->H`

is arithmetically sound, since its antecedent is false under the ordinary
equality interpretation. It yields the original witness
`U(d,E(H,d)->1)->1` when a proof of `H->1` is available.
An infinite primitive recursively generated family of refutable formula codes
could therefore serve as ordinary variable labels. This does **not** immediately
give the inherited PA calibration.

The negative-property reverse rewrite requires the witness `exists x_a E(b,a)`;
therefore restricting its external `b` to refutable labels looks sufficient.
However the diagonal neighborhood bridge introduces
`z0 = code(E(a,b))`, which is generally not refutable. It then uses
`E(z,z0)->(P(z0)->P(z))`. The inherited proof of that reverse congruence needs
`exists x_z E(z0,z)`, and the weakened witness does not supply it. Separators
whose labels are arbitrary formula codes cause an analogous closure issue.
Consequently this is a research proposal, not a calibrated Con(PA) machine.

## A safe logical variant, not physically optimized

One can replace the old first head by `B(d,H)` above, and replace the separate
diagonal head by

`J(C,A)=((Gamma(C)->1)->A)`, where `Gamma(C)=C->U(C,C)`.

The two parameters must range independently. The resulting seven-head calculus
is exactly equivalent to the original one:

1. Under the assumption `1`, positive weakening gives `Gamma(C)->1`, so `J(C,A)`
   yields arbitrary `A`. Discharge the assumption to obtain explosion.
2. Set `A=Gamma(C)`. The axiom becomes `(Gamma(C)->1)->Gamma(C)`. Positive Peirce
   yields `Gamma(C)` without any use of quantifier rules.
3. `B` and explosion recover the old first head by its known finite template.
4. Conversely the old head gives explosion and `B`; `Gamma(C)` and explosion
   prove `J(C,A)` by deduction.

Binding `C` to `D` and `A` to `H` in the AX interface covers both parameters
independently. This changes a real logical interface, but probably adds emitter
operations. No state count or novelty claim is made without compilation and a
corpus search. Tying `A=C` would be invalid: the resulting formula does not
recover the separate diagonal schema.

## A useful scheduler theorem

Let commands act on a state space S, with a halt outcome; let every finite
refutation p have a primitive recursively constructed command word W_p halting
from every s in S. Let V be any fixed finite command word. Then V;W_p also halts
from every s: either V already halts or W_p halts from the state left by V.

Therefore completeness needs only a scheduler covering every suffix after the
fixed prefix V. In particular a forced initial Shift followed by all command
words is complete. Soundness is unchanged because the same sound commands are
executed. For a physical optimization, the fresh-candidate branch must be shown
to initialize the exact remaining suffix, and the restricted coding must be
proved to enumerate all suffixes. The all-store hypothesis avoids any need to
reset work registers between candidates.

This permits an implementation to omit decoding a known first command if that
command can be entered directly. It does not prove that such an implementation
uses fewer states; the fresh branch and source-address scanner must be counted
and checked together.

## ZFC and ConciseIPRA lessons

The useful transferable ZFC mechanism is contextual state sharing, coupled to
source association and fixed helper reuse. Reducing source instruction count
alone does not bound physical working states. All incoming histories and
simultaneous fold interactions need proof.

The ConciseIPRA native scalar core illustrates moving logical rules into
constructors and computation, but its equiconsistency target is iPRA, not PA.
Replacing the searched calculus by that kernel would change the target unless
a new PA-refutation translation were supplied. Full-formula induction could
produce an HA-strength target and a negative translation could relate PA and
HA refutations, but no suitably small compiled binary machine is established
by that observation.

## Small experiment: coefficient eight

A local attempt replaced the radix-5/6 helper by a four-increment helper and
used it twice for coefficient eight. The baseline seven AX folds remain, but
the additional runtime fold `41 -> 99` used by the radix-5/6 construction fails
its exact local certificate. Thus adding the helper gives 195 states by this
route, not a new 194-state construction. Coefficient changes for arbitrary
radix at least four already have a general calibration in the corpus; changing
the coefficient alone would be a weak novelty claim.
