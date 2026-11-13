# Independent review: eager opening in the strict three-field checker

## Scope of the result

The proposed composition preserves the native public theorem language by a semantic soundness argument and canonical completeness. It does not preserve all arbitrary accepted raw certificate traces, and it changes no arithmetic or logical axiom. Its bi-interpretation with iPRA is inherited through the existing native-calculus bridge.

The baseline is the three-field protocol in incoming `ipra_validated_three_field_2026-11-13`, with the eager opener and empty administrative premise already justified separately by incoming `ipra_checked_reduction_2026-11-13`.

## Public validation

At the initial call the context is empty. A permitted list arity is 1 or `2+d%2`; a scalar must be an odd nonnegative integer less than the current odd depth. The whole-input printed-character gate independently restricts every JSON value to exact integer/list trees. On an invalid scalar, the eager opener evaluates the missing-image sentinel even at an even depth, so validation cannot silently erase an invalid formula leaf. On a valid public tree the opener preserves every leaf and every constructor.

The addition of `[]` to the context occurs only after this initial traversal. Thus context emptiness still separates the public validation phase from the proof phase.

## Semantic opening

In the proof phase replace the old fallback by `d%2 * i(t,d=3)`. This validates the image before multiplying it. At odd depth the result is the validated numerical image. At even depth the result can be integer 0 or the empty list, according to the image's type; both have the auxiliary reading `0=0` at a formula position. This is the already-proved eager-opening lemma, combined with the uniform-zero convention `a or 1` for retained leaves.

In particular, the argument never assumes the false Python identity `0 * [] == 0`. The claim is equality of auxiliary readings, not equality of arbitrary raw trees.

## Soundness of the three-field protocol

The existing soundness induction uses only semantic opening, closure/freshness, a true neutral resource, and the zero-instance supply lemma. All are preserved by the eager opener and empty neutral. The endpoint-match branch reconstructs and then recursively proves its equality or closure major; the major remains at the old floor. Elimination at a unary major opens the corresponding closure at the fresh parameter. Introduction keeps the distinction between `u=[]` (cases) and `u=0` (equational progress), and the witness is checked before the floor decreases.

The computation branch may add an instance H(b) that is not itself an arithmetic axiom. Its zero instance H(0) is a computation axiom by the existing zero-instance computation lemma. The continuation's conclusion and old hypotheses do not contain b. After the induction hypothesis in the ordinary realization, substitute zero for b and cut away H(0). This supplies the inference without improperly treating H(b) as an axiom or using unproved substitution admissibility in a syntactically restricted calculus.

The empty neutral has auxiliary reading `0=0`. It therefore gives no new public consequence. Repeated additions or context aliasing add only this theorem.

## Canonical completeness and the exact recoding needed

Use the inherited canonical compiler with zero represented by scalar 1. Numerical term fields are therefore true-valued, including numerical zero. Retain all numerical zero codes, computation predecessor fields, closure-specialization source fields, and introduction mode markers.

Recode the administrative source `s=0` to `s=[]` only in nonmatching introduction records (case or progress), where the recursive major call is meant to close on the neutral premise. This recoding is necessary because the new context contains `[]` rather than scalar 0.

Do not globally replace `s=0` by `[]`: closure specialization uses `i(template,0)`, and `i(template,[])` need not yield the same raw minor formula. The proof accepts a branch-aware recoding, not an indiscriminate textual transformation of certificates.

At canonical computation and introduction records, a numerical term cannot be identical to a formula ending in a binary equation, so the endpoint-match test does not select an accidental elimination. At canonical transport/specialization records the intended endpoint match holds. Every additional eager image validation succeeds on these properly scoped canonical images. Computation hypotheses are closed at the old floor, so fresh versus zero opening makes no difference on canonical instances. The compiler then proceeds by induction on the native proof tree.

These arguments give precisely the accepted public theorem language of the existing native calculus. Finite fixtures are useful regression evidence but are not the proof of this universal statement.

## Normalized terminal composition

The separate proposed byte-profile change opens the complete terminal computation candidate instead of putting `or 1` into its counter field by hand. Its soundness follows from the established closed-candidate and plus-opening lemmas: a successful no-image opening is closed, has the same auxiliary reading, and reads as a computation axiom. The eager version can reject some additional raw aliases, which does not affect soundness.

Canonical completeness requires the inherited branch-aware terminal compiler: when an early terminal closes a call, omit all discarded subproof packets, so those packets cannot later be consumed by a parent continuation. The existing canonical term/template depth bounds guarantee that each added eager validation succeeds. This is again public-theorem equivalence, not equality of all raw accepted stacks.
