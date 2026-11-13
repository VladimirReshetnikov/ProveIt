# Independent review of the forward index binding

The proposed source composition has the right theorem directions, coordinate
order and fact hypotheses as inspected; no concrete source-level mismatch
remains. It is unelaborated and its proposed rank and c cast identities are
explicit premises, not established model bindings.

At a valuation v, the source sets `w j=v j+1`. The pinned 71/60 model join
sends its positive-shifted zero to the 67/94 positive-shifted zero at that
same v. The qualified theorem `ObjectCurrentEquation2011.internalZero_positiveShift`
is indeed declared in `CurrentEquationSyntax2011.lean`; it supplies the
unshifted 67/94 zero at w. Both that namespace and
`AdaptiveEquationSyntax2011` define the shift by the same substitution and
`InternalZero` by the same split-natural equality. Their definitional
conversion in this client remains an elaboration question.

The extraction theorem takes that positive w and zero and returns the five
ordinary equations. The client's 14 witness arguments, four fixed ports and
five hypotheses match `ordinary_first_indices`; its result includes
`2*R<c` for the same natural definitions of rank and c. The separate
`scalar_window` application uses the same transport equation and yields the
positive gap. The fourth port is consistently the natural cast of
`highPort+beta`, shifted once. `current_bounds` provides the stated fixed-port
inequalities. The local source files and prospective 71/60 provider are pinned;
this is not authentication of their resolved transitive Lean objects.

For the signed-ring corollary, both `hrank` and `hc` are assumptions. Given
those equalities, `ι_lt_ι` has the direction needed to transport the natural
strict half inequality. The missing rank equality is substantive: natural
`q−1`, `q−F`, and `q²−1` are truncated. Positive beta and J give `q>=1`,
while the positive scalar gap gives `F<=q`; those facts allow the respective
natural subtractions to correspond to signed subtraction. The port casts and
all four coordinate/term identities still need proof in the same model. The
checker includes finite controls with `q>=1,F<=q` and a negative control
showing the failure of raw subtraction when `F>q`; these do not prove the
model cast.

The auxiliary norm, f and A bounds, a model-natural positive shear coordinate,
the literal child evaluator, the reverse zero map and iPRA endpoint remain
separate. The source contains proof tactics, but neither they nor import
selection, elaboration or axiom reports were run here.

Reproduce the two receipts from `Computability/DiophantineConsistency`:

    set -o pipefail
    timeout 30s python3 -I -S -B research/current2011-shear-forward-index-binding-draft/check.py | cmp - research/current2011-shear-forward-index-binding-draft/result.json
    timeout 30s python3 -I -S -B reviews/current2011-shear-forward-index-binding-independent/check.py | cmp - reviews/current2011-shear-forward-index-binding-independent/receipt.json

No Lean, build, staging, or source mutation was performed.
