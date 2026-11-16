# PA194 target membership substitution

In every candidate-PRA model with IΣ₁, `membershipVacuity_target` extracts the
membership-vacuity target proof from the actual guarded seed, assuming exactly
`c ≠ a` and `c ≠ b`. `specializeWithMirroredEquality_target` gives a fixed-size
target proof of the displayed universal specialization from two explicit target
provability hypotheses: vacuity of the target formula under the quantified label
and primitive-equality rewriting from the quantified atom to that target.
`negativeSpecialization_target` derives a negative membership specialization using
the two displayed label inequalities, the guarded membership-vacuity theorem,
and two still-explicit target-provability hypotheses: primitive-equality rewriting
from q to p, and vacuity of q under the quantified label. The formulas, labels and
proof witnesses can be nonstandard model elements.

These are target-calculus derivations, not assumptions that PA proves their
premises. They do not yet provide unconditional positive membership substitution,
general universal instantiation, arbitrary source-proof compilation,
physical-machine simulation or either consistency implication. The retained-overlay
same-output source replay is not an empty-overlay build.

`reverseAll_target` gives target-provable reverse membership rewriting for the
first, second and diagonal membership slots, uniformly in every candidate-PRA
model with IΣ₁ and for all model-valued labels, including label collisions and
nonstandard elements. `reverseRight_target` and `reverseLeft_target` state the
two primitive-equality membership directions explicitly. The proof ports the
guarded-separation argument to the model-uniform target calculus: it derives
membership vacuity and negative specialization from the previous module, proves
that its separator code is strictly larger than the relevant labels, uses the
actual guarded-seed and diagonal proof rules, and handles all collision cases.
The final reverse-rewriting theorems have no additional rewriting, vacuity, or
label-distinctness assumptions.

These are target-provability statements about primitive `eqValue`, not yet
substitution for the translated `neighborhoodValue`, an internal compiler for
arbitrary source proofs, physical-machine simulation, or either consistency
implication. The replay uses a retained overlay, not an empty-overlay build.

The universal membership-implication theorems combine guarded-seed membership
vacuity, mirrored-equality specialization and the unconditional primitive reverse
rewriting proof. `neighborhoodRightCongruence_target` and
`neighborhoodLeftCongruence_target` then derive substitution in either target
membership position from neighborhood equality, under exactly the explicit
reserved-label inequalities `z ≠ a`, `z ≠ b` and `z ≠ c`. No extra
proof-valued rewriting or vacuity hypotheses remain.

`sourceAtom_substitute_container` and `sourceAtom_substitute_member` connect the
result to both actual numeric source atom decoders. They prove target-provability
of the translated equality implying the appropriate implication between translated
source membership atoms, with the reserved label distinct from the three decoded
term labels. The code identities are algebraic and accept raw terms; validity and
source-scope conditions must still be established by the caller. The theorems are
uniform in nonstandard model-valued terms, environments and labels, in every
candidate-PRA model with IΣ₁.

These are fixed-size target proof recipes; they do not yet prove arbitrary source
proof transport, source-axiom compilation, physical-machine simulation or either
consistency implication. The combined audit also imports the independent path-graph
branch to check diamond-import compatibility, and is a retained-overlay suffix
replay, not an empty-overlay build.

`allocated_sourceAtom_substitution` proves both membership-position substitutions
using the actual source equality and membership atom decoders at a common allocated
bound stack. It assumes valid source terms a, b, c; both the equality atom `(a,b)`
and membership atom `(c,a)` have codes ≤ the allocation ceiling; the binder depth
is ≤ that ceiling; `base + ceiling ≤ reserve`; and the initial bound stack and
free stack give labels strictly below reserve at every index ≤ ceiling. The theorem
derives the three label inequalities needed for target substitution from those
explicit assumptions. Terms, codes, environments and depth may be nonstandard
model elements.

The result concerns fixed source-atom substitution proof recipes in candidate-PRA
models with IΣ₁. It does not prove these assumptions for every source-proof use,
compile arbitrary source proofs, simulate the physical machine or establish either
consistency implication. The source replay uses a retained overlay, not an empty
overlay build.

`path_sourceAtom_substitution` considers two model-valued paths from the same root
reaching respectively the encoded equality atom `(a,b)` and membership atom `(c,a)`.
The proof derives both source-atom code bounds and the allocation-depth bound from
the paths. It assumes valid source terms a, b, c; that the two paths have the same
binder count; `base + root ≤ reserve`; and that initial-bound and free-stack entries
at every index ≤ root are strictly below reserve. Equal binder counts give the same
reconstructed bound stack. Under these assumptions, the theorem proves both
actual numeric atom-decoder membership substitutions in the target calculus.

The paths, terms and indices may be nonstandard model elements. The theorem does
not show that arbitrary PA-proof uses supply the two paths, that their binder depths
coincide, or that the remaining environment assumptions hold for those uses. It
does not compile arbitrary source proofs or prove a machine consistency implication.
The combined audit also imports the path-graph branch to check diamond compatibility
and uses a retained overlay, not an empty-overlay build.

Run `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-substitution.sh --out DIR` with matching retained prerequisites.
