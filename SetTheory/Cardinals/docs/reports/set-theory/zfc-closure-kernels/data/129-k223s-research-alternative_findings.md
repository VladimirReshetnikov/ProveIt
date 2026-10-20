# Theory and encoding alternatives: findings and limits

The delivered 223-state candidate uses the seed-request K theory with the
universal presentation of the request, the inherited membership-code equality
helper, a reordered bundle, explicit double-negation fusion, and a source grammar
that preserves the predecessor's context-dependent decoder aliases. Its source
has 4,962 primitive instruction occurrences and 209 distinct source
subtrees (including leaves), compared with 4,799 and 210 in K224. Formula length increased while the
actual state count decreased. The seed form itself is an existing intermediate
in the pinned K230 proof; its use for source-program sharing is the new step.

## 1. Calibrated K formalisms

Use the definitions of Sub, W and H from `theory223.tex`.

| Formalism | Ordinary core | Calibration and implementation status |
|---|---|---|
| Output-root K | `forall a,x exists C ((phi(x,a) -> R(x,C)) and H(C))` | Pinned K230 theory; K224 is the released predecessor. |
| Seed-request K | `forall a exists C (W(a,C) and H(C))` | Upper reduction is `KPSeed.v / output_root_to_seed`; lower reduction is `KPrimeCore.v / seeded_core_to_kp0` followed by the K0 quotient interpretation. The selected source and actual 223-state table use this form. |
| Factored K0 | For each a, C has support and W(p,C) whenever `p=a` or `exists u in C Sub(p,u)` | The inherited lower proof already goes through this theory. Compiling its explicit disjunction and equality test was not needed for the successful machine; no smaller K0-only table is claimed here. |
| Conditional K | `forall a,x (phi(x,a) -> exists C (R(x,C) and H(C)))` | Calibrated in the K224 archive by a two-marker hereditary-domain interpretation. Its reported direct constructor screen reached 212 DAG nodes. This is an inherited source-search result, not a lower bound and not a claim about all grammars. |
| Conditional K with active labels 0,1 | Same conditional body at fixed native roles, including matrices with codes 0,1 | The K224 archive supplies the low-code calibration, using an interpretation with every object nonempty. Its best reported screened source had 219 DAG nodes. Fewer parameter pushes did not imply fewer distinct binary subtrees in those trials. |

The support-free weakening has a different status. K224 supplies an explicit
rational-order model of its full ordinary schema, with irreflexivity; a
nonnegative rational version also supplies an empty object. ZFC proves that
model exists and hence proves consistency of the support-free theory. If ZFC
is consistent, that theory cannot provide a ZFC-provable equivalence with
Con(ZFC), by the second incompleteness theorem. This is a mathematical
obstruction to that particular deletion, not an impossibility result for other
weakenings or encodings.

Primary inherited references are the K224 report's sections on conditional K,
fixed roles and deleting support, and these retained files:

- `portable/theory/conditional_k_calibration.md`;
- `portable/theory/native_fixed01_calibration.md`;
- `portable/baseline226/vendor/k230-rocq/coq/settheory/KPSeed.v`,
  `KPrimeCore.v`, `KP0.v`, `KQuotZFTransfer.v`, and `KQuotZFC.v` in the nested
  K225 archive.

## 2. Equivalent request forms

Writing `B(p,C)=exists y(phi(y,p) and R(y,C))`, the unchanged private-label
condition ensures B is closed in the output role. Classical logic then gives

    forall y(phi(y,p) -> B(p,C))
      <-> ((exists y phi(y,p)) -> B(p,C))
      <-> (not B(p,C) -> not exists y phi(y,p)).

The first form is used in the delivered 223 machine. Both alternatives are
calibrated at all enabled native triples by the exact named decoding and the
separate coincident-role proof; their equivalence is not an unsupported
alpha-renaming of numerical formula codes.

The generator constructs 720 original expressions: three root forms, two
orders for each of three conjunctions, six bundle orders, and five helper
choices. It separately constructs 1,440 existential-premise and contrapositive
request variants. The uniform decoder-side-condition audit passes for all
2,160 generated expression trees. That audit covers constructor exceptions,
not source compilation, runtime or proof-theoretic strength of every changed
helper implementation.

Only six variants of the two alternative request forms were screened through
our grammar search around the selected seed layout:

| Helper | Request presentations screened | Best observed weighted grammar score | Distinct subtrees, including leaves | Maximum zero run |
|---|---|---:|---:|---:|
| R(a,b) | Existential premise and contrapositive | 199 | 210 | 6 |
| Q(a,b) | Existential premise and contrapositive | 200 | 210 | 6 |
| E(a,b) | Existential premise and contrapositive | 200 | 210 | 6 |

These observations are recorded in `request_screen/results.json`. The weighted
score accounts for which inherited decoder-sharing patterns survive; it is not
itself a working-state count. None of these six was promoted to a complete
new table. There is no exhaustive optimality claim for the other generated
request variants, other bundle grammars, or deeper grammar-search beams.

## 3. Canonical equality binders

The inherited restricted-helper calibration accepts any computable label
builder kappa satisfying

    a != b implies kappa(a,b) != a and kappa(a,b) != b.

There is no restriction on the diagonal. In particular I, R, Q and E in either
argument orientation all qualify. Positive-tag constructors dominate both
endpoints. I has only the permitted collision I(0,0)=0. The simpler arithmetic
labels a+b+1 and P(a,b)+1 also dominate both endpoints and qualify mathematically.
This calibration preserves an actual helper family; replacing it only by
primitive symmetry is not justified by this argument.

Here are exact metrics from our *direct helper substitutions in the unchanged
K224 formula layout*, before a global grammar search:

| Binder kappa(a,b) | Primitive occurrences | Distinct subtrees, including leaves | Maximum zero run |
|---|---:|---:|---:|
| R(a,b), control | 4,799 | 210 | 6 |
| Q(a,b) | 4,800 | 210 | 6 |
| E(a,b) | 4,801 | 210 | 7 |
| I(a,b) | 4,798 | 211 | 6 |
| a+b+1 | 4,753 | 212 | 6 |
| P(a,b)+1 | 4,796 | 215 | 6 |

The E substitution initially looked attractive because the helper becomes an
(E,E) constructor pattern. In the tested layout it did not reduce the DAG
count and made the zero-run requirement worse. The addition-only builder
shortened the primitive word substantially while increasing the number of
binary subtrees, because its implementation could not reuse as much of the
existing constructor code. These are measured source tradeoffs, not state
counts for independently certified machines. The delivered candidate retains
R(a,b).

The generic helper theorem is in the pinned K224 files
`portable/theory/k_equality_helper_extension.md` and
`portable/theory/source116/proofs/general_kappa_equality_helper.md`.

## 4. What remains open

The search does not establish a minimal Turing-machine encoding. Several
remaining directions require fresh implementation work and have no new state
count in this contribution:

- Compile the explicit K0 requests using a different elementary source
  language or a proof calculus with cheaper equality/disjunction.
- Design a theory-aware grammar optimizer that searches equivalent matrices
  and program reassociation jointly, accounting for decoder context, the
  blank reset limit and retained alias patterns at every step.
- Change pairing or formula tags together with their arithmetic constructors,
  total decoder, parameter enumeration, proof cutoff and startup. Counting
  characters in an alternative syntax does not measure those costs.
- Compile a finite class theory or finite set-theoretic axiom basis from the
  beginning. Such a project needs a pinned first-order axiom string, a
  concrete theorem enumerator and complete state accounting; no smaller
  NBG, Levy--Vaught, combinatory-logic or universal-interpreter machine has
  been constructed in this theory branch.

The positive result is therefore specific and reproducible: an existing
calibrated seed form exposes useful repeated source blocks, and one selected
weighted grammar turns them into an actual 223-state candidate. The negative
results document particular mathematically weak deletions or measured
compilation layouts; they do not limit what a different compiler may achieve.
