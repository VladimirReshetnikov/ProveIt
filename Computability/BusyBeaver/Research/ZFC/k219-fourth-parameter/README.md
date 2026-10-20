# Which computed fourth parameters remain worth testing?

**Current correction:** the proposed `U=R(A,B)` calibration is now ruled out by
an explicit ZFC-formalizable syntactic consistency proof. The
[Lean-checked invariant](diagonal-invariant/README.md) also proves that this
calculus cannot derive `F → truth`. It retains every native seed/support
bundle and even allows all identities and quantified monotonicity. Assuming
ZFC is consistent, no ZFC-provable consistency equivalence with ZFC can hold
for this modification. The earlier conditional semantic arguments below
remain valid; a model-existence implication strong enough for calibration
cannot be proved in ZFC from this consistency, assuming ZFC is consistent.
The [prior version](diagonal-invariant/history/prior-README.md) is retained. Ordinary extensions rule out `R(B,A)`, `R(A,C)` and `R(C,A)`;
only `R(A,B)` has been Lean-checked here. The new
[six-orientation extension](six-orientations/README.md) also rules out
`R(B,C)` and `R(C,B)` by ordinary syntactic proofs, treating each fixed
orientation separately. The later [five-value model](finite-matrix/README.md)
strengthens this to their union and arbitrary membership fourth-input builders
simultaneously, with an ordinary PA-formalizable consistency proof. That new
model does not validate K or explosion.

Replacing rho8's independent fourth parameter by a formula built from the
other three would remove an input read. The existing HC countermodel excludes
far more such replacements than its five originally stated examples. A
membership-headed replacement escapes that particular semantic obstruction,
but `R(A,B)` is now excluded by the stronger syntactic invariant above.
There is no new machine in this note.

## A uniform obstruction

Write the native propositional row as

`L(A,B,C,U) = ((C → U) → A) → ((A → C) → (B → C))`.

Keep every other K219 row, the full gated seed-K bundle with support, MP,
GEN, and truth code 0. One may also add identity, ex falso, and the K
combinator. Replace unrestricted rho8 by any collection of families
`L(A,B,C,f(A,B,C))` satisfying the following **pointwise code condition**:

For every input triple, `f` returns code 0, code 1, one of the three input
codes, or a code whose outer constructor is implication, quantification,
or equality. The builder may inspect the numerical inputs, choose different
cases, use arbitrary internal subformulas, and choose any binder labels.
There is no polynomial, term-size, or uniform outer-constructor restriction.

**ZFC proves consistency of every such restricted calculus.** Thus, assuming
ZFC is consistent, these modifications cannot have ZFC-provable consistency
equivalence with ZFC. The conclusion concerns refutations of the single native
falsum code 1; allowing nonstandard or junk codes does not avoid it.

The proof extends the submitted
[Source 140 full HC countermodel](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/140-k219-res-theory-restricted_rho8_strong_countermodel.md).
Use exactly its domain, assignment semantics, colored membership, and all
non-rho8 soundness arguments. In its four-valued implication algebra, with
sole designated value 3, the **only** failures of L are

| A | B | C | U | L |
|---:|---:|---:|---:|---:|
| 0 | 3 | 1 | 2 | 0 |
| 1 | 3 | 1 | 2 | 0 |

Implication never has value 2: its image is `{0,1,3}`. Quantification and
equality have image `{0,3}`. Code0 has value 3, including its exceptional
implication alias, and code 1 is always0. Finally, when `(A,B,C)` has either
bad pattern in the table, none of the three input values is2. Consequently
the builder's result cannot supply the required value 2 in either bad case.
Every emitted restricted instance is designated under every assignment.

All the other native rows and the **entire** K schema are unchanged, so the
same HC model and induction on finite derivations prove consistency in ZFC.
No syntactic substitution principle or classical completeness is assumed.
For a precise arithmetized theory, take an effective, ZFC-provably total
builder with a ZFC proof of the pointwise condition; equivalently permit
every instance satisfying the decidable code condition. Its consistency
also covers any effective subfamily by inclusion.

This rules out every pure implication term in A/B/C/F/truth, of any size,
and any construction with an outer Q or E. It also covers code-dependent
selection among those alternatives. It does not exclude a different
three-parameter basis, a changed K schema, or a genuinely new membership
atom used as U.

## A code-dependent membership proposal

Consider instead

`U = R(A,B) = 4 P(A,B) + 1`,

where the numerical **formula codes themselves** are the two variable
labels. This has three independent input fields and makes no claim that
U faithfully represents an arbitrary fourth formula. It is permitted by
the user's consistency-only objective. The stronger syntactic result above
now rules out the requested
ZFC-provable consistency equivalence, assuming ZFC is consistent.

One direction is immediate: every new rho8 instance is an instance of the
old unrestricted schema. A finite proof in the proposed calculus is
therefore already a proof in the original calculus. Consistency of the
original implies consistency of the proposal. The reverse direction cannot
supply the requested ZFC-provable
calibration, by the syntactic consistency result above. The following
conditional model arguments remain valid on their explicitly stated domains.

The inherited HC model provably fails this family. Choose distinct
`p,q ∈ HC`. The antichain encoding supplies a coordinate k with
`e(q)(k)=0` and `e(p)(k)=1`. The fiber `n⁻¹(k)` is uncountable, so choose z
outside the countable set `p ∪ q ∪ {p,q}`. Then the model's colored
membership gives `r(z,q)=1` and `r(z,p)=2`.

Assign labels `0↦p`, `1↦z`, `2↦z`, `3↦q`, and choose native codes

`A=1=R(0,0)`, `B=0=truth`, `C=73=R(2,3)`.

The proposed builder returns `U=5=R(1,0)`. Their values are respectively
`0,3,1,2`, so the emitted L has value 0. This works for any choice of the
antichain coloring and uncountable-fiber map used in Source 140's construction.

Failure of this one model is only a reason to investigate the proposal.
It does not prove equiconsistency, exclude a different weak model, or
justify a halting-independence claim. In particular, a metatheorem allowing
arbitrary renaming/substitution cannot be silently imported: changing A or
B also changes U's variable labels. A successful proof must handle that
literal coupling, low codes, and the unchanged K private-code coupling.

## The proposal forces this matrix semantics to become classical

There is a stronger conclusion within the same semantic framework. Take
any nonempty domain D and any relation `r : D × D → {0,1,2,3}` with
`r(x,x)=0`. Keep the implication table, ordinary Boolean equality, and
the Boolean designatedness-based quantifiers from Source 140. If this
assignment interpretation validates every proposed R(A,B) row, then the
image of r cannot contain **both** 1 and 2.

Indeed, if `r(w,q)=1` and `r(z,p)=2`, assign the four labels independently
as `0↦p`, `1↦z`, `2↦w`, `3↦q`. The same native instance with codes
`A=1`, `B=0`, `C=73`, `U=5` has value 0. There is no requirement that the
four domain elements be distinct.

Thus either every atomic relation value avoids 1, or every atomic relation
value avoids 2. Each of the resulting three-element sets `{0,2,3}` and
`{0,1,3}` is closed under implication, and on each set

`(a → b) = 3` iff `a ≠ 3` or `b = 3`.

Equality and quantification already have Boolean values. Structural
induction therefore identifies designatedness of **every native formula**
with its ordinary classical interpretation under membership `r(x,y)=3`.
The exceptional code 0 and its implication alias agree. All enabled K
bundles consequently have their original classical meanings. Any model
of the full proposed calculus in this matrix framework supplies an
ordinary model of the unchanged native K theory with irreflexive membership.

This eliminates the entire nonclassical matrix-model route used for the
five restrictions, rather than merely one choice of coloring. It is still
not a consistency calibration: there is no completeness theorem here
saying every consistent modified calculus admits a model in this special
matrix framework. A different algebra or a different interpretation may
still give a weak full model.

## A general condition that would recover the original row

The code trick also gives a useful conditional result for arbitrary truth
value algebras, independent of Source 140's four-element table. Suppose
implication is interpreted by a fixed binary operation on a set V, atoms
by `r : D × D → V`, and every value in V is attained by r. Interpret
validity as designatedness under every assignment, as usual.
Require compositional native implication, including compatibility of the
exceptional code 0 alias: its truth value t satisfies `imp(t,t)=t`.

Take the fixed native input codes

`A=9=R(0,1)`, `B=73=R(2,3)`, `C=201=R(4,5)`.

The builder returns `U=13905=R(9,73)`. The eight labels
`0,1,2,3,4,5,9,73` are distinct. For any four values a,b,c,u in V,
surjectivity of r supplies four witnessing pairs of domain elements.
Assign those pairs to the four disjoint label pairs. Validity of this
single proposed native axiom instance therefore forces L(a,b,c,u) to be
designated. Thus unrestricted rho8 is valid at **every** quadruple of
truth values. The rest of the native calculus is unchanged.

Consequently any such atomically surjective model of the proposed theory
already models the original theory. A lower-bound calibration could try
to prove that a consistent proposed calculus has a model with this property,
or prove a syntactic counterpart. Neither is established here. Arbitrary
matrix semantics need not be atomically surjective; closing that gap is
the research problem, not an assumption one can omit.

## Fresh formula-code labels remove the Boolean-quantifier assumption

A further [semantic argument](fresh-label.md) exploits the literal coupling
in `U=R(A,B)`. For a nonzero formula code B, variable label B is fresh from
that formula. In the instance A=C=truth, changing the assignment at label B
to the value at label 0 preserves the formula's value b and makes R(0,B)
irreflexive. The row becomes `L(t,b,t,0)=I(t,I(t,I(b,t)))`. Under the stated
single-designated-value implication laws, validity forces `I(b,t)=t`.
The zero code follows from the truth alias.

This implication-to-truth law holds for every realized native formula value,
without atomic surjectivity, a designated membership edge, or Boolean
quantifier output. Together with Boolean negation and designatedness-based
quantification, it allows one-way extraction of the full ordinary seed-K
schema, including support. The exact `req/clos/nks/bundle222` definitions
were checked: the argument needs the bare negative K component and does not
assume that both conjuncts can be projected from the raw bundle. Recursively
translated quantifiers receive double negation to keep matrix values Boolean.

The separate [Lean file](FreshLabel.lean) checks the conditional fresh-label
lemma and the negative-core projection. Its [actual receipt](fresh-label-lean.json)
records a successful build; the first theorem uses only `propext`, and the
second has no axiom dependencies. Native support, the full K extraction and
model existence are not formalized in this small file. The earlier
[Boolean-Q analysis](history/analysis.md) is retained as superseded history.

The earlier gap was a ZFC proof that consistency of the proposed code-coupled
calculus produces a model with one designated value,
Boolean negation and the specified implication/quantifier laws. Ordinary
classical completeness cannot be invoked to supply that missing strength.
This is a conditional model-extraction result, not equiconsistency.

## Evidence and next test

A separate [singleton algebra search](singleton-search/README.md) tested all
78,732 three-value implication/quantifier/equality assignments, including
non-designated equality and non-Boolean negation, with the literal full seed
bundle. It found no restricted or unrestricted model. This excludes only
that bounded constant-atom, shared-quantifier family; it does not establish
the proposal's consistency calibration.

The [finite checker](check_range.py) evaluates all 256 unrestricted instances,
384 safe-choice cases, and the explicit native counterexample above. Its
[receipt](result.json) records the exact scopes. The unbounded HC argument
and the construction of z remain mathematical proofs. The separate
[Lean file](Range.lean) kernel-checks the exact two failures, the implication
range, the safe-choice lemma, both classical three-value restrictions,
the arbitrary-domain one-color-absent lemma, and the conditional richness
argument with its eight literal labels. It does not formalize the
native syntax, structural induction, HC, or the consistency comparison.
The [Lean receipt](lean-result.json) and [log](lean.log) show all eight
declarations checked with standard axioms only: `propext`, and for the
arbitrary-domain disjunction also `Classical.choice` and `Quot.sound`.
The conditional richness theorem has no axiom dependencies.
No `sorryAx` remains in the checked file. The first unsuccessful elaboration
is retained under [history](history/lean-attempt1/result.json).

Reproduce into a new output file, from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-fourth-parameter/check_range.py \
  --output /tmp/k219-fourth-range-fresh.json
lean Computability/BusyBeaver/Research/ZFC/k219-fourth-parameter/Range.lean
```

The [source measurements](../k219-pivot-fusion/README.md) now include all
12 ordered membership/association layouts, with a minimum of 205 distinct
subtrees. [Selective allocation](../k219-continuation-search/README.md)
reaches 222 raw states for those layouts. The `R(A,B)` consistency calibration
is ruled out as above; a smaller
verified implementation of it would not meet the objective. Other proposals
need their own calibration and implementation. Syntax savings alone are
insufficient. The accepted
[219-state construction](../candidate-k219/README.md) retains unrestricted
rho8 and is unaffected.

Attribution: the implication algebra and full HC construction are from the
K219 submission, imported as Source 140 from commit `26d5de6d21`. The general
range obstruction and the R(A,B) counterexample above are follow-up deductions
made during this repository's minimization work on 20 October 2026.
