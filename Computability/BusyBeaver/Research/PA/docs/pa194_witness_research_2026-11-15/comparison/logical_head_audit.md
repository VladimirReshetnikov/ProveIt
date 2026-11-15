# Audit of the new witness and disjunctive heads

This note records an independent review of the finite logical certificates. It does not claim a new Lean kernel theorem or a verification of the literal TM. The corresponding compiled emitter still needs its complete source, physical, and blank-start certificates.

## Definitions and retained proof resources

Write `I(a,b)` as `a → b`, `N(a)=a → 1`, and `U(d,a)` for universal quantification in the numerical calculus. Let

- `W(d,h)=U(d,N(E(h,d)))`;
- `X(d,h)=U(d,N(U(d,h)))`;
- the old witness head be `h5(d,h)=W(d,h) → 1`;
- the old first head be `O(d,h)=(X(d,h) → 1) → h`;
- the new independent witness head be `h5X(d,a,h)=W(d,h) → a`;
- the contraposed first head be `C(d,h)=(h → 1) → X(d,h)`;
- the shorter disjunctive head be `J(d,h)=(X(d,h) → h) → h`.

The parameter `a` in h5X is independent of both `d` and `h`. This independence is essential. Merely changing the consequent to the old witness parameter h is not the same schema.

The unchanged restricted rho8 basis uniformly derives K, S, and Peirce. These remain named derived rules in the supplied finite certificates. There is no truth-table proof oracle. All other admitted schema names are checked directly against their defining term trees; modus ponens checks exact formula matching; generalization checks its input proof and binder. The replay rejects unlisted rules and any open-assumption line. The J replay additionally restricts the schema set separately for each direction.

The relevant retained quantifier resources are

`Gamma(a): a → U(a,a)` and
`h6Q(d,a,h): U(d,a → h) → (U(d,a) → U(d,h))`.

These are used at specific unrestricted numeric parameters, including 0 and 1. No freshness side condition is silently added.

## The noncircular explosion bootstrap

Set `e=E(0,1)` and `w=U(1,e → 1)=W(1,0)`. The following derivation uses no old first head:

1. K gives `1 → (e → 1)`.
2. Theorem generalization gives `U(1,1 → (e → 1))`.
3. h6Q and MP give `U(1,1) → U(1,e → 1)`.
4. Gamma(1) is `1 → U(1,1)`.
5. Compose steps 4 and 3 to obtain `1 → w`.
6. h5X(1,a,0) is `w → a`.
7. Compose to obtain `1 → a`.

When both compositions are expanded into K/S/MP, this has exactly 16 Hilbert lines. The replayed rule census is: Gamma 1, Gen 1, K 3, S 2, MP 7, h5X 1, h6Q 1. There is no h1, old h5, or Peirce invocation. The only generalized theorem is a closed K instance, so there is no generalization under a dependent hypothesis.

The old calculus derives h5X by composing old h5 with its established explosion theorem. Conversely h5X recovers old h5 at a=1 in a single line. Thus replacing only h5 preserves the entire theorem set, with finite uniform proof translations.

If the first head is also changed, the new explosion proof remains available before using any classical formula transformation. This repairs the bootstrap defect in the older standalone contraposed/dual-head proposals.

## The shorter J head

For arbitrary x and h, the two formulas `(x → 1) → h` and `(x → h) → h` express the same disjunction once 1 has the requisite explosion behavior. Here x is the specific nested quantified term X(d,h).

**O implies J.** Assume `x → h`. To obtain h, assume additionally `h → 1`. Compose the two assumptions to get `x → 1`, and apply O to get h. Discharge the second assumption to obtain `(h → 1) → h`. Peirce at `(h,1)` yields h. Discharge the first assumption to obtain J. This direction does not need explosion at all: it uses only O, K/S, and Peirce.

**J plus h5X implies O.** The bootstrap already gives `1 → h`. Under the assumption `x → 1`, composition gives `x → h`; J then gives h. Discharging the assumption yields O. This direction uses no Peirce, original h1, or original h5.

The machine-readable certificates are:

| Certificate | Lines | Permitted resources |
|---|---:|---|
| `j_certificates/h1_to_J.json` | 95 | old h1, K, S, Peirce, MP |
| `j_certificates/J_to_h1.json` | 72 | J, h5X, Gamma, h6Q, theorem Gen, K, S, MP |

Both are assumption-free after deduction expansion and both replay successfully. The builder is `j_certificates.py` with its local `hilbert_builder.py`; the separately structured checker is `verify_j.py`. Its result is `j_certificate_replay.json`.

A direct emitter count is useful but is not a literal state count. With symbols D, H, A, C=cons, P=push, i=increment, the common term X has word `HDCiiPiCDCii` (12 tokens). Old O appends `PiCHC`, giving 17 tokens. J appends `HCHC`, giving 16. The old h5 word has 16 tokens, while h5X has 15. The coupled replacement therefore saves two macro tokens before grammar optimization. The consequence for the number of physical readers depends on compatible folds and the full compiled association.

The other positive-disjunction orientation `(h → X(d,h)) → X(d,h)` is also equivalent, but repeats the large X term. It is a compression experiment, not an immediate source-length saving.

## The 15-token three-parameter head J_A

A further safe weakening removes the remaining hard-coded negation constant from J. Define

`Y(d,a,h)=U(d,U(d,h) → a)` and
`J_A(d,a,h)=(Y(d,a,h) → h) → h`.

The parameter a is independent. At a=1, J_A is literally J. To derive all J_A instances in the old calculus, set p=U(d,h). Old explosion gives `1 → a`, which yields `(p → 1) → (p → a)` by pure implication composition and deduction. Generalize this closed theorem in d and apply h6Q, obtaining `X(d,h) → Y(d,a,h)`. Under the assumption `Y → h`, composition gives `X → h`; apply the already derived J to obtain h, then discharge the assumption. No assumption is generalized. The reverse direction instantiates J_A at a=1 and applies the preceding J plus h5X argument.

| Certificate | Lines | Permitted resources |
|---|---:|---|
| `ja_certificates/old_to_JA.json` | 358 | old h1, h6Q, theorem Gen, K, S, Peirce, MP |
| `ja_certificates/JA_to_h1.json` | 72 | J_A, h5X, Gamma, h6Q, theorem Gen, K, S, MP |

The generator `ja_certificates.py` and direction-restricted checker `verify_ja.py` reproduce these certificates; `ja_certificate_replay.json` records both passing. The 15-token word is `HDCiiACDCiiHCHC`. Compared with the original O and h5 pair, J_A plus h5X saves three direct emitter tokens. As before, this is a source-word reduction, not a machine-state conclusion.

## Why the analogous witness relativization fails

It is not safe to replace old h5 by the superficially similar family

`U(d,E(h,d) → a) → a`.

There is a counterexample even in PA's binary-membership interpretation. Let d=0, h=1, a=M(0,2), with variable assignment x0=1, x1=0, x2=1. The quantified premise says that for every x0, if x0=x1 then x0 belongs to x2. This is true because 0 belongs to 1. The consequent is the assertion that 1 belongs to 1, which is false. The failure is capture of the d-variable occurring in a. Restricting a to the numerical binder code d restores a freshness fact, but does not provide the arbitrary old h5 instances; no uniform recovery is supplied for that restricted experiment.

## Uniformity in iPRA

The displayed transformations are finite templates whose leaves are parameters and whose operations are constructor application, finite proof concatenation, and previously retained uniform proof suppliers. The finite certificate checker verifies their syntactic equations for symbolic parameters; it does not evaluate the numerical formulas or a truth predicate. Interpreting those term trees by the primitive-recursive numerical constructors therefore gives a uniform proof transformation for every natural tuple, including tuples represented nonstandardly in a model of the weak arithmetic.

Replacing old/new axiom leaves and preserving MP and theorem Gen yields primitive-recursive translations of complete numerical derivations in both directions. Their correctness can be stated using quantifier-free Boolean trace checks and verified by the same induction on proof-list length as the retained proof compiler. This supplies the logical-calculus equivalence component. It does not alone supply the missing command semantics, physical simulation, scheduler fairness, PA translation, or literal arithmetic halting theorem. Those must be composed from the explicitly named retained calibration and the new machine's own certificates.

This is why the argument distinguishes a finite checked proof template from an end-to-end proof-assistant theorem. The revised AX11H written iPRA calibration is substantial mathematical input, while the current primary PA194 Lean arithmetic endpoint remains conditional.

## Prior-art check within the pinned corpus

The pinned source was searched across 18,266 distinct text payloads and 24 distinct recursively encountered ZIP payloads. The first broad witness/head search returned 125 payloads for manual filtering. The reproducible extended search, including disjunctive-head terms, returned 132 payloads; its locator list is `logical_prior_art_hits.json` and its driver is `search_logical_prior_art.py`. No occurrence of the independent-consequent schema W(d,h)→a was located. This is a scoped search result, not a universal claim of priority.

The closest prior variants differ materially:

- `docs/conpa_tm_comparison_and_search/research_ipra/newsearch/head_weakenings.py` searches W→1, A→(W→1), and W→(A→1). It does not use W→A.
- The corresponding `support/work/logic/logical_search_notes.md` fuses h1 and h5 only with an additional explicit explosion head; its combined word has 207 tokens and its best observed AX-body grammar score is 75.
- `docs/pa194qn_research_2026-11-13/research/logical_emitter/h5_search.txt` changes the equality witness parameter, not the independent outer consequent.
- `docs/incoming/pa194_research_2026-11-14.zip`, member `search/modal_heads/modal_head_equivalence.tex`, already names the formula here called C and the modal orientation H→U(D,N(U(D,N(H)))). Those standalone experiments do not provide the new bootstrap. The archived classical double-negation equivalence argument cannot be applied before explosion is recovered.
- The old `proof_notes/h1_bootstrap_constraints.md` has an `argOr` variant substituting an implication-encoded disjunction for H throughout the old head. That is different from replacing only the outer negation in O to form J.

The general corpus census, rather than name matching, should determine whether a compiled candidate table is new up to the tested graph symmetries.

## A ruled-out rho8 shortcut

A further proposal restricted the first two offset parameters to coincide, leaving only

`R3(d,a,h)=((h → d) → d) → ((d → h) → (a → h))`.

R3 alone, MP, and the numerical truth alias do not derive the retained K/S/Peirce basis. A three-valued counteralgebra has designated value 0 and implication table

| → | 0 | 1 | 2 |
|---|---:|---:|---:|
| 0 | 0 | 1 | 1 |
| 1 | 0 | 0 | 1 |
| 2 | 0 | 1 | 0 |

All 27 R3 instances are designated. MP preserves designation because row 0 produces 0 only in column 0; I(0,0)=0 respects the truth alias. K at `(a,b)=(2,0)`, S at `(a,b,c)=(1,0,2)`, and Peirce at `(a,b)=(1,2)` are undesignated. A numerical valuation can assign a non-implicational atom such as E(0,0) to value 2, so the failed K instance is realized by actual numerical codes. `rho_diagonal_matrix_search.py` and its JSON record the independent finite enumeration. This obstruction is for the proposed implicational basis by itself; it does not claim a countermodel of all other numerical heads added together.
