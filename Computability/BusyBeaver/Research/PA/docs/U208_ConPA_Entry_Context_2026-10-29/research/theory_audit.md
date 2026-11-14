# Independent audit of U, the native calculus, and the consistency endpoint

Date: 2026-10-29. Scope: ordinary mathematical review of the actual source
manuscripts downloaded from ProveIt at
`343da82d7384d10ec9fd1c17361fc923b2d1d117`. This is an internal research note,
not an exported PA derivation or a new proof-assistant certificate.

## Findings

1. I found no concrete defect in the unary U interpretation argument after
   reading the full lower and upper proof, including the delicate ordering of
   induction, least failures, successor existence, and graph histories.
2. The manuscript proves a substantial ordinary mathematical theorem; it is
   inaccurate to classify its least-failure construction as an unproved
   hypothesis. Its claimed internal endpoint is
   `PA |- Con(U) <-> Con(PA)`, supported by uniform syntax transformations and
   PA induction. No arbitrary-proof translator or proof-assistant endpoint is
   delivered for that theorem.
3. The five full U209 research packages retain exactly the same theory ZIP,
   with SHA-256
   `0fcb1117a5353766a3366bab04e56b4efbd0607833cdc73ffb34b67e6808b0ff`.
   Their reductions change physical machines and source associations; they do
   not present competing theories U. The sixth incoming archive is PDF-only.
4. The literal U209 machines search the inherited native numerical calculus
   for unrestricted weak cover W plus global irreflexivity IR. They do not
   execute the unary report's separate positive dyadic stream.
5. The strong final theorem needs four independently identified links: literal
   machine to source continuation; source continuation to native refutation;
   native refutation to W+IR refutation; and the W+IR/U/PA proof translations.
   The already formalized K215/ZFC theorem supplies none of these changed-U
   endpoints automatically.

## Precise unary theory

The language is classical equality-free first-order logic on nonempty domains,
with one binary predicate E. Let

    Sub(x,a) := forall z (E(z,x) -> E(z,a)).

For every formula phi with free variables contained in {x}, U contains

    forall a exists b [
      forall x (E(x,b) -> phi(x)) and
      forall x (Sub(x,a) -> (phi(x) -> E(x,b))) ].

This is weak covering, and a cannot occur freely in phi. In particular, the
usual exactification phi(x) := Sub(x,a) and psi(x) is illegal here.
There is no bound on the number of bound variables, formula size, or
quantifier complexity. No global extensionality is assumed.

## Independent check of the lower proof

Read in `sources/pa_unary_power_cover/pa_unary_power_cover/sections/`:
`overview.tex`, `unary_core.tex`, `unary_arithmetic.tex`,
`unary_separation.tex`, `upper_transport.tex`, `positive_interface.tex`,
`emitter.tex`, and `stream.tex`.

Coextensionality x~y means equality of their member profiles. It is always
congruent in membership's second coordinate; saturation supplies the first
coordinate congruence needed inside numerical objects. Numericality N includes
saturation, transitivity, a strict class order, saturated members, and least
and greatest endpoints for every nonempty represented intersection at every
initial cutoff. It asserts neither external well-foundedness nor external
finiteness.

The local predecessor lemma does not need total successor. An empty object
exists by false filtering. Numericality is hereditary to members. For a
nonempty number n, endpoints give a greatest member d and the full profile
`z in n iff z in d or z~d`; this is its predecessor. Existing successors are
numerical, injective on classes, and never empty. The saturation uses in
heredity and the successor construction are supplied explicitly.

The induction argument uses a cover of unary failures at a numerical source
n. Since each member x of n is a subset of n, failures inside n are selected
exactly. If some selected member exists, its least class has a predecessor
where the step gives a contradiction. If no selected member exists, n itself
is a least failure and its predecessor supplies the contradiction. This
second case avoids the otherwise circular use of a successor of n.

Arbitrary parameters are internalized in the legal unary predicate

    Q(v) := forall p (BaseAndStep(theta,p) -> theta(v,p)).

Its base and step follow from their respective premise components. This even
yields induction for predicates not invariant under coextensionality; the
proof needs a strictly smaller predecessor, not a saturated failure object.

Only after induction does the proof establish global numerical comparison and
least tuples. Given a target chi(z,n_1,...,n_k), bounded comprehension assumes
both invariance in the numerical parameters and an available support source
containing every selected z as a subset. If the target has no exact output at
some tuple, minimize the failure predicate and bind its entire least tuple
inside the unary matrix. Equivalent least tuples select the same profile.
Applying the cover at a separately chosen support makes it exact and produces
the contradiction. There is no truth predicate or semantic search hidden in
this argument.

Total successor and exact powers of numerical sources follow. Saturated
singletons, pairs, and Kuratowski pair profiles collect all representatives,
so their coordinate decoding works modulo coextensionality. Pair codes with
coordinates in n are subsets of an exact power W of n, giving the support
for graph comprehension.

The old history in canonical graph extension/restriction is bound by an
existential quantifier. All free graph-comprehension parameters are numerical.
Pointwise history uniqueness is proved first, using the already derived
induction with arbitrary ambient parameters. Thus graph witnesses do not
become illicit free parameters of unary matrices. A separate numerical value
bound handles nonmonotone transitions. Successor iteration gives addition;
addition iteration gives multiplication; the full translated PA induction
schema follows from representative induction.

## Upper interpretation and formalization strength

In PA interpret E(x,a) as Bit(a,x). PA proves Sub(x,a) implies x<=a.
For each fixed translated matrix, PA induction constructs a binary
characteristic code on [0,a]. This verifies even unrestricted weak covering,
and `2^a>a` gives global irreflexivity. The argument holds in every PA model:
it is formula-specific induction, not a uniform satisfaction predicate.

Both directions use fixed interpreting formulas and uniform finite derivation
templates. Renaming, substitution, formula relativization, term-graph
translation, and proof concatenation are primitive recursive. Formula and
proof-length induction supply the advertised PA-verifiable refutation maps.
I found no need for a reflection principle or a consistency assumption in
those syntactic maps. A fully formal syntax implementation is still missing;
that is a formalization limitation, not an identified gap in the conventional
mathematical interpretation proof.

The orbit model in `unary_separation.tex` also appears sound. It separates
unary weak covering from the stronger source-parameter schema and from exact
arbitrary-source filtering; it does not weaken the numerical construction.

## The positive stream is a separate interface

The positive theory uses D := forall v E(v,v), a source diagonal q(a), and
the negative seed not D. Falsity in a unary matrix is replaced by *closed D*,
not q(a); the latter would illegally introduce a source parameter.
Its localized filters initially require irreflexive supports. All lower-proof
supports are numerical or exact powers W of numerical n, and those W are
irreflexive: n in W, while W in W would force W subset n and hence n in n.

The positive fragment by itself has a one-object total-relation model.
The calibration is nonderivability of its designated atom, or consistency
after adding the negative seed, not ordinary consistency of the fragment.

Its dyadic codec has target code 0 and an independent nine-pairing polynomial
emitter. The U209 native codec instead has truth alias 0 and falsity target 1.
Constructor counts or polynomial degrees from the positive interface cannot
be imported as a proof or state bound for a U209 transition table.

## Native-calculus and source lineage inspected

The complete U222 paper and selected logical source templates are in

    sources/U209_ConPA_Composed_2026-10-29/
      U209_ConPA_Composed_2026-10-29/reference/U222_ConU_2026-10-28.zip

I extracted this to `work/theory_lineage/U222_ConU_2026-10-28/` and read
`u222_consistency_machine/paper/report.tex`, especially the native-code and
calibration sections, plus `references/logic/README.md`.

The compact U212 ancestry is extracted under `work/theory_lineage/combined/`.
I directly read its `baseline/u214/proofs/role_emitter.tex` and
`baseline/primary_u213/proofs/compiler.tex` and `startup_suffix.tex`.

The actual numerical calculus uses Cantor P, I=4P, R=4P+1, Q=4P+2,
and auxiliary equality 4P+3. Its deliberate alias I(0,0)=0 and diagonal
target R(0,0)=1 require normalization, and the source discusses both.
The native logical bridge preserves membership vacuity and interprets
auxiliary equality by two-sided membership indiscernibility, rather than
assuming unavailable primitive-equality vacuity. The retained Rocq files
are reference excerpts with missing imports, not a complete U project.

The role-a emitter uses a both as matrix code and output label, b as source,
and c as tested label, with gate c!=a,b. Positive matrix codes have all
effective labels below a; code zero is closed truth. Thus output freshness
holds even at the alias. For a!=b the guard is subset. For a=b, the guard
becomes emptiness under IR; covering at an existing empty source proves that
collision case. Padding a desired matrix to n>1 and using (a,b,c)=(n,0,1)
supplies completeness. I found no missing exceptional-code case in this
written calibration.

The correct consistency cycle is

    Con(PA) -> Con(W+IR) -> Con(U) -> Con(PA).

Each arrow is a proof-translation statement, not merely an appeal to
standard-model equiconsistency.

Blank startup enters an interior AX suffix. The incoming cached 1 is an
arithmetic selector and cannot be assumed theorem-valued. The suffix proves
nine explicit theorem heads over opaque tail4, and the all-natural
Cantor-diagonal credit theorem bounds subsequent debt from candidate1 by2.
The seven-head margin protects the unsafe tail. Ghost list length is needed
because P(0,0)=0; the proof retains it explicitly.

The strong source compiler works above arbitrary incoming top and numerical
stack after reset. Its raw-zero exception in J(0), and its reserved disposable
zero for the cache-return MP alternative, are explicit. Successful candidate
codes are cofinal, and unsuccessful candidate evaluation terminates. These
facts justify completeness beyond the nontrivial startup cutoff.

## Already-present negative results; do not rediscover as savings

`u209_compatible_folds_2026-10-29/report.tex` gives small-code obstructions
to deleting either gate for the unchanged emitter. Removing c!=a allows
(a,b,c)=(0,1,0), forcing diagonal membership under IR. Removing c!=b allows
(0,1,1), forcing a universal object and contradicting IR.

`U209_ConPA_2026-10-29/report.tex`, section 8, gives a stronger no-go theorem
for deleting the whole dominated propositional row: assign membership 0,
auxiliary equality 1, quantification the body's value, and implication Boolean
equality. Truth and all retained rows/bundles are designated; MP and GEN
preserve designation; target1 is not. PA can verify this by primitive-recursive
formula evaluation and induction on finite derivations, so the reduced
calculus is PA-provably consistent and cannot preserve Con(PA) calibration
if PA is consistent. The displayed counterinstance to the deleted row is
a=b=c=u=1, which respects u<=a.

## Recommended final claim for a new smaller machine

First prove and document the specific new result

    PA |- Halt(M_new,blank) <-> Halt(M_selected_parent,blank),

with the arbitrary-exterior local identities, contextual invariants,
source-equivalence and/or universal primitive contracts actually used.
Then compose with the inherited mathematical calibration to state

    PA |- not Halt(M_new,blank) <-> Con(U) <-> Con(PA).

The second line is the conventional PA-formalizable endpoint of the full
chain. Label the machine a candidate with executable proof evidence unless
an end-to-end kernel-checked statement has actually been produced. Do not
claim unconditional nonhalting, global minimality, or that bounded test runs
establish either consistency or nonhalting.
