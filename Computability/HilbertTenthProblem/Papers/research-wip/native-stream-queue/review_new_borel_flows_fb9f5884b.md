# Borel flows intake at fb9f5884b

This is an independent full-text mathematical intake, with a fresh metadata
check. No substantive error was found in the manuscript's stated flow and
time-one theorems. One malformed source cross-reference is retained below.
The manuscript supplies a useful support criterion for finite calculations,
but no ordinary-integer Diophantine compiler, fixed witness count, paid
operation count, or Turing-universality construction.

## Immutable source and exact coverage

The archive is `docs/incoming/Borel_Flows_Glazer_ProveIt.zip` at commit
`fb9f5884b0a53eb2a950bc564b9a0aa9bed65df8`, parent
`555ee36fbdb3b786efe766ae2406466ba3e40229`, Git blob
`458e8534343b05968f8c9f8eae661ed8da73fb4a`. Its 362,023 bytes have SHA256
`78af94354498216718974f9c4974c0efeffda16aef19e9d49896459db429f135`.
There are nine regular members, all under `Borel_Flows_Glazer_ProveIt/`.
The companion JSON authenticates every member, its size, CRC and SHA256,
all eight shipped checksum entries, and each inclusive read span.

The following texts were read completely:

| Member | Inclusive lines | Read mode |
|---|---:|---|
| `borel_flows.tex` | 1–1724 | Full mathematical text, appendices and bibliography |
| `README.md` | 1–86 | Full guide and declared scope |
| `CLAIM_LEDGER.md` | 1–63 | Full claim/status ledger |
| `SOURCES.md` | 1–87 | Full provenance and stated external-read record |
| `verify.py` | 1–270 | Inert code only |
| `verification_results.json` | 1–63 | Saved evidence only |
| `build.sh` | 1–11 | Inert commands only |
| `SHA256SUMS` | 1–8 | Full manifest; all entries independently hash-checked |

The PDF was hashed only. It was not rendered, read, rebuilt, or checked for
the claimed page count. No supplied program, build command, frozen helper,
or copied predecessor program was executed or imported. The author's saved
normal/optimized-run and PDF-build claims remain attributed to the author.

Applicable instructions were read in `Algebra/SurrealNumbers/AGENTS.md`
1–182 and the incoming retention rule in `docs/incoming/README.md` 426–438.
For context, at the same immutable arrival commit, the
`polish-models-of-omnific-arithmetic/README.md` 18–60 and `article.tex`
36434–36476 were read. These identify source 23 / Part XVII and its
conjugacy and flow questions; this is not a new audit of that entire host.
All these Git blobs and read spans are in the receipt.

The exact cited BCH repository pin was independently authenticated:
commit `c39974f12a45c8795575ab222f3b84b2901c394f`, tree
`dbbe29a67da59205e50a264c58a9bc3731d761ec`, and
`Algebra/BakerCampbellHausdorff/Lean/BCH/Formal/Trunc.lean`, blob
`5f238ed2f05b54e940e51f974465768c0dc23ba7`. Its complete 1–143 lines were
read inertly. The truncated word representation and coefficient-recovery
declarations are present. This establishes the source interface, not a
Lean build, axiom audit, or formal verification of the new flow theorems.
External papers listed in `SOURCES.md` were not independently read in this
intake; their findings, priority, and the author's external inspection
claims are not independently certified here.

## Mathematical scope and proof challenge

The standing field has real coefficients and supports finite below every
real bound, with a nonzero countable **divisible** ordered subgroup
`Gamma <= R` of exponents. A flow is jointly coefficient-Borel on
`R x L_Gamma` and consists of unital field automorphisms. These hypotheses
are used in the proofs, not optional presentation choices.

The following are the principal points independently challenged in the
complete read. They record why the conclusions pass in this setting.

1. **Field, windows and category, lines 197–406.** Divisibility supplies
   square roots of positive elements, making the order algebraically
   recognizable. A bounded exponent window is a countable-dimensional
   direct sum, generally not finite-dimensional. The finite-orbit-span
   theorem proves the latter property for individual group orbits: a
   minimum-dimensional finite space with nonmeagre orbit preimage has
   an open stabilizer, hence the whole connected group stabilizes it.
   The overlap of two translates is taken inside suitable open sets,
   so the minimality argument is not an assertion that arbitrary
   nonmeagre sets must intersect. Borel finite-dimensional matrix
   representations then become continuous. No finite-dimensionality of
   an entire exponent window is assumed.

2. **Automatic normalization, lines 407–485.** Each coefficient of a
   Borel additive map on real constants is linear over the reals; the
   image of 1 fixes those constants. Order determines the valuation,
   and an ordered additive automorphism of an Archimedean subgroup of
   R is multiplication by a positive scalar. For the flow the scalar
   is Borel and has countable image, so its logarithmic additive
   homomorphism is zero. This proves valuation preservation before
   window methods are used.

3. **Exact generator classification, lines 486–665.** Compatible finite
   orbit spaces permit coefficient differentiation and ensure the
   derivative is still left-finite. The Leibniz argument uses input
   cutoffs `b-c` and `b-a` when the factors have lower bounds `a,c`;
   it does not use a false same-window product rule. Conversely,
   real-linear valuation-nondecreasing derivations with finite cyclic
   spaces on every window give compatible matrix exponentials.
   The finite span of products is invariant under the derivation, so
   the finite-dimensional differential equation proves multiplicativity.
   General zero-gain coefficients can require convergent real exponential
   series. They are not asserted to be eventually finite formal sums.

4. **Strictness and rank, lines 666–919.** In a finite invariant space,
   strictly increasing valuation is nilpotence, by its finite set of
   leading exponents. Hence strict integrability is equivalent to
   escape of iterated monomial valuations, with arbitrary series handled
   by the tail lemma. Finite rational rank gives a minimum positive
   basis gain in the strict case; finite-rank nonnegative-gain maps use
   a common left-finite monoid of positive shifts. At infinite rank the
   rationally independent chain can increase inside `(1,2)`. Its
   successive monomials stay in one bounded window and are independent.
   Strict increase therefore fails to give integration. The chain is
   proved using rational independence, not a floating-point test.

5. **Shears and nonclosure, lines 920–1083.** Each alternating shear
   acts by rational binomial expressions on the exponent basis and has
   the required support and tail control on the entire field. The two
   individual flows integrate. Their sum and bracket have nonescaping
   monomial chains. For the product of their time-one maps, the integer
   orbit of the first chain monomial has successive largest indices
   `2k-1` with nonzero coefficient. Its span in `[1,2)` is infinite.
   This excludes every Borel-flow embedding of that product, not merely
   a chosen logarithm or an attempted BCH expansion.

6. **Time-one existence and uniqueness, lines 1084–1238.** On a finite
   invariant space, a basis with distinct leading exponents gives a
   triangular matrix with positive diagonal. Canonical real powers
   use this positive spectrum and nilpotent parts. Real exponential
   polynomials agreeing at all nonnegative integers agree identically;
   this proves compatibility and multiplicativity. A putative Borel
   flow likewise has real triangular infinitesimal data. Thus uniqueness
   does not assume the false global complex logarithm inverse law.
   The tangent-to-identity logarithm is controlled separately by
   window-local nilpotence.

7. **Parameter space and applications, lines 1239–1393.** The integrable
   strict locus is Borel by a countable monomial/cutoff/iteration formula
   and Borel evaluation. This is not a decision procedure. A common
   positive gain for several operators supplies a cutoff for all words
   in those operators; individual local nilpotence alone does not.
   The surreal interpretation is set-sized and conditional on the
   specified realization. There is no extension to the whole surreal
   class hidden in that argument.

The verification discussion and all questions/end matter, lines
1394–1724, were also read. The open questions explicitly keep effective
recognition, log extraction, joint operator conditions, sharper Borel
complexity, and certificate production separate from the proved
classification. No source conjecture has been silently converted into
an established effective procedure.

## Relationship to the conjugacy intake and computation goal

There is no byte-identical regular member shared with
`Borel_Conjugacy_Divisibility_Threshold.zip` at
`62846e17a78ee588f0d3686c966c1cde9a0f1bb9`; the fresh checker compares all
regular-member hashes. Mathematical overlap includes the rational-rank-one
divisible setting. The conjugacy manuscript allows intermediate groups
`Z <= Gamma <= Q`, often nondivisible, with an explicit ordered-automorphism
condition; this flow manuscript assumes divisibility but permits arbitrary
countable rational rank. Neither result makes the other hypotheses free.

In particular, the new review-side halting-height construction in the
conjugacy intake produces a generally nondivisible Gamma. Its
co-c.e.-complete zero-gain conjugacy slice does **not** automatically
transfer to this flow paper's divisible setting. No such transfer or new
undecidability theorem is claimed here.

The constructive interface here is a support-certified finite calculation.
With a known common gain `delta > 0`, operator words of length `n` cannot
contribute below output cutoff `b` once
`v(input) + n*delta >= b`. Finite invariant window spaces supply another
finite calculation. The manuscript does not give a uniform effective
producer for those spaces, their spectral data, or a gain certificate from
arbitrary Borel codes. Real coefficients and arbitrary exponent-group
descriptions are additional data, not free integer operations. Even after
restricting them to effective encodings, translating the finite calculation
into a fixed-arity unbounded-history integer graph and charging every loader,
guard, power and arithmetic producer remains unsupplied. No paid compiler
improvement follows from the classification, the formal word interface, or
the 5,372 finite tests.

## Retained finding and finite evidence

There is one minor literal source defect at `borel_flows.tex` 167–168:

```text
Theorem~
ef{thm:timeoneexact} then gives an exact, unique-embedding
```

The intended reference is `Theorem~\ref{thm:timeoneexact}`; the label is
properly defined at line 1127 and its theorem is proved. This is an editorial
finding, not a mathematical counterexample. It can be corrected explicitly
when the article is placed, while retaining the immutable original archive
and this finding. No archive rewrite, adapted article or PDF rebuild is
part of this intake. Because malformed literal text is not a reference
command, a successful undefined-reference check would not detect it.

The source has 66 distinct labels and 69 recognized simple reference
commands using 36 distinct targets; all those targets resolve. This census
is not a general TeX parser or a substitute for the complete text read.

The saved JSON reports PASS and 5,372 checks: 1,656 basis/chain, 1,200
polynomial/shear, 1,760 time-one, and 756 rational-binomial checks. The fresh
metadata checker verifies only their arithmetic total and the saved pivot
list. The supplied program was read but not run. The saved tests cannot
establish Baire-category, infinite-support, or classification statements;
the review of those claims above is a proof challenge.

The only executed artifact for this intake is the newly authored
`review_new_borel_flows_fb9f5884b.py`, using the standard library and
read-only Git commands. It authenticates the immutable ZIP and context
bytes, manifests, exact read spans and recorded metadata. Fresh normal and
optimized runs were compared exactly before freezing. Its receipt pins the
helper's own source bytes. No external mathematical result, whole Lean
development, PDF, or supplied execution is certified by that PASS.
