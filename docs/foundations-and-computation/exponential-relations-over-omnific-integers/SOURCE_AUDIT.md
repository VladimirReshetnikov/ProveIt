# Source and claim audit

Article: **Exponential Relations over Omnific Integers: Exact toric kernels, decidable fragments, and one-scale elementary cores**.

Prepared 23 September 2026. This file records provenance and the scope of the checks; it is not an independent referee report.

## 1. Classical inputs

### Surreal normal forms and the exponential of purely infinite surreals

**H. Gonshor, An Introduction to the Theory of Surreal Numbers**, London Mathematical Society Lecture Note Series 123, Cambridge University Press, 1986. Chapters 5, 8, and 10. DOI: https://doi.org/10.1017/CBO9780511629143.

The book is the underlying source for Conway normal forms and the ordered surreal exponential. The official Cambridge chapter information was checked. For the precise normal-form and exponential statements, the accessible survey below was inspected.

**V. Mantova and M. Matusinski, Surreal numbers with derivation, Hardy fields and transseries: a survey**, Contemporary Mathematics 697 (2017), 265–290. DOI: https://doi.org/10.1090/conm/697/14057. Preprint: https://arxiv.org/abs/1608.03413.

The inspected PDF's Theorems 2.10 and 2.16 give the relevant normal-form and exponential statements. PDF pages 7 and 11 were visually checked. The required exponential fact is the bijection between the additive purely infinite group and the multiplicative group of Conway monomials:

```text
exp(J) = {omega^gamma : gamma in No}.
```

It is NOT the false pointwise formula `exp(p)=omega^p`. All our arguments use only the image statement, injectivity, and the exponential homomorphism law.

### Classical Lindemann–Weierstrass

**S. A. Popescu, A simple and self-contained proof for the Lindemann–Weierstrass theorem**, arXiv:2306.14352, version 2, 17 September 2023: https://arxiv.org/abs/2306.14352v2.

The version-2 abstract states the exact classical theorem used: exponentials of distinct algebraic complex numbers are linearly independent over the algebraic numbers. This is a modern exposition, not a new attribution of the classical theorem. The article imports the theorem explicitly; it does not re-prove or computationally validate it.

### Presburger arithmetic

**R. Cluckers, Presburger sets and p-minimal fields**, Journal of Symbolic Logic 68(1) (2003), 153–162. DOI: https://doi.org/10.2178/jsl/1045861509. Preprint: https://arxiv.org/abs/math/0206197.

Section 1.1 recalls the language and its quantifier-elimination and decidability facts; PDF page 2 was visually checked. Our manuscript verifies directly the integer-division property for the additive group of omnific integers and then uses these classical logical results. The rational-slope reduction is therefore a definitional expansion of a standard decidable theory, not a new proof of Presburger's theorem.

### Ordered vector spaces and effective algebraic numbers

**J. Loveys and Y. Peterzil, Linear o-minimal structures**, Israel Journal of Mathematics 81(1–2) (1993), 1–30. DOI: https://doi.org/10.1007/BF02761295.

This is relevant background. The particular ordered-vector-space quantifier elimination used in the article is proved directly, by eliminating linear equalities and finitely many order bounds; no stronger theorem from this paper is imported silently.

**H. Cohen, A Course in Computational Algebraic Number Theory**, Graduate Texts in Mathematics 138, Springer, 1993. DOI: https://doi.org/10.1007/978-3-662-02945-9.

The official Springer publication and computational topics were checked. The article uses standard effective algebraic-number representations, exact field operations, equality/sign tests, and rational-basis arithmetic. Approximation programs alone are explicitly not accepted as uniform substitutes for algebraic-number codes.

### Undecidability

**S. Salehi, Computation in Logic and Logic in Computation**, 2016: https://arxiv.org/abs/1612.06526.

**T. Kurahashi, Incompleteness and undecidability of theories consistent with R**, 2022: https://arxiv.org/abs/2211.15455.

These are modern sources for classical arithmetic undecidability. Our negative result explicitly interprets ordinary integer arithmetic. A separate explicit halting-problem reduction proves the nonuniformity of decision from arbitrary real approximation names. Neither argument is an existential-only undecidability proof.

## 2. Repository inspection and comparison boundary

Repository: https://github.com/VladimirReshetnikov/Surreal.

Pinned commit:

```text
958b5c4865819bd55ea1f5ffc050282aea7ef570
```

The GitHub connector retrieved the recursive tree, report catalogue, and selected relevant report material at that commit. In particular:

- `docs/README.md`: the catalogue distinguishes the project's AI-assisted drafts, proof-review status, and formalization coverage. It was used to avoid the already heavily developed ring-quotient and embedding directions.
- `docs/surreal/set-sized-quotients-of-omnific-integers/article.tex`: the introduction and main-result discussion establish that constant-term quotients, large quotients, normalization, and related ring arithmetic were already being developed. Only the relevant portions were inspected; this extensive manuscript was not audited in full.
- `docs/surreal/exponential-automorphism-rigidity/README.md`: the report overview and verification boundary distinguish its automorphism/valuation rigidity from the exponential-equality language considered here. The complete mathematical report was not re-verified.

No conjectural theorem from these reports is used as an input in the present article. The normal-form/exponential statements are attributed to the external classical sources instead.

A connector code search for `Presburger` returned no items but flagged `incomplete_results: true`. This is inconclusive and is NOT evidence that the repository contains no related result. The repository comparison is targeted, not exhaustive, and no claim of priority over every repository manuscript is justified by that search.

The user-supplied Wikipedia article on surreal numbers was opened for orientation. It is not used as an authoritative source for the proof-bearing steps.

## 3. Novelty search and claim classification

Targeted web searches included combinations of:

```text
"omnific integers" "exponential" "decidable"
"surreal" "Lindemann" "Weierstrass"
"omnific" "Presburger"
"purely infinite" "elementary" "exponential"
ordered abelian group irrational scalar multiplication decidable theory computable real
"omnific" "exponential relations"
"ordered vector spaces" "Turing degree"
```

The returned material supplied background and adjacent topics but did not establish an exact prior statement of the manuscript's combined classifications. These searches were limited. Failure to retrieve a prior statement is not proof of novelty. Related ordered-group, scalar-expansion, and computable-model-theory literature may contain equivalent formulations.

The following distinctions govern the claims:

| Result family | Classification in this delivery |
|---|---|
| Conway normal forms, Gonshor's exponential, Lindemann–Weierstrass, Presburger elimination | Classical inputs, explicitly credited |
| Group-algebra kernels, monomial independence, linear quantifier elimination | Standard mechanisms proved or explained in the needed form |
| Independence on `Qbar + J`, exact toric kernels and constant-field intersections | A proposed surreal/surcomplex application and synthesis, not a new classical transcendence theorem |
| Algebraic-affine exponential-equality decidability, definable coordinate splitting, rectangular normal form | Proposed classification results for the precisely specified language |
| All elementary substructures and elementary embeddings, countable one-scale cores | Proposed consequences with complete proofs for that language only |
| Exact fixed-slope Turing degree and nonuniform approximation-name obstruction | Proposed explicit classification; uses classical computability mechanisms |
| Nonlinear-predicate undecidability | A language boundary proved by interpreting ordinary arithmetic |
| Arbitrary real-base fiber description | A structural transfer over ordinary integer equations, not a solution of the base equations |
| Further research questions | New proposals in this manuscript, not represented as previously named open problems |

Independent specialist review is still required for both mathematical correctness and priority. No named longstanding conjecture is asserted to have been settled.

## 4. Mathematical dependency and edge-case checks

The audit during preparation specifically checked the following points.

- The finite independence theorem groups by distinct purely infinite parts BEFORE applying ordinary Lindemann–Weierstrass within each block.
- Normal forms are supported on sets. No proper-class sum, group algebra, or field generated by a proper class is treated as a set-sized algebraic object.
- `Qbar + J` is an additive exponential domain with finite algebraic imaginary parts. It is not claimed to be a complex algebra or the domain of a global surcomplex exponential.
- In the exact constant-field theorem, the subgroup of ordinary arguments is saturated in the finitely generated argument group. A direct-sum complement is therefore available; its purely infinite parts are rationally independent.
- Balanced partitions require equality inside each block but do not require inequality between different blocks. Zero coefficients and the empty sum cause no exception.
- In `n+p`, the purely infinite coordinate is the primary order coordinate. The constant-term map is not order preserving.
- Irrational algebraic slopes are allowed inside exponential EQUALITY predicates, not as unrestricted scalar multiplication on the integer sort and not as irrational-slope inequalities there.
- The integer and vector sorts split definably, and quantifier elimination is stated in that coordinate expansion, not falsely in the original one-sort signature.
- The one-scale structures are not subfields. Their elementary status refers to external relations on an additive group.
- For a fixed irrational real, the equivalence of the polynomial-sign oracle and its cut is nonuniform: algebraic and transcendental cases use different fixed-parameter reductions. This is stated prominently.
- The halting-coded family of slopes consists entirely of algebraic irrationals with uniformly valid approximation names. It does not supply minimal polynomials or root-isolating algebraic codes uniformly.
- The nonlinear undecidability proof defines the ordinary integers with quantifiers before interpreting multiplication; no existential-only conclusion is drawn.
- The arbitrary real-base theorem leaves ordinary integer exponential equations untouched. Purely infinite positivity does not imply positivity of the ordinary constant term.

## 5. Actual finite verification

Command:

```sh
python3 code/checks.py --output check_results.json
```

The recorded run is deterministic, standard-library-only, and uses exact rational and quadratic-field arithmetic. It passed 22,074 cases:

| Test family | Cases |
|---|---:|
| Exhaustive balanced partitions versus coefficient grouping | 7,381 |
| `exp(x)+exp(y)=2` | 729 |
| Product-factorization example | 729 |
| Two-term multiset equality | 6,561 |
| Square-root-of-two pure-part detector | 49 |
| Quadratic-coordinate splitting | 2,000 |
| Homogeneous real-base fiber sign patterns | 4,000 |
| Anchored real-base fiber sign patterns | 625 |
| Total | 22,074 |

Exactly 1,000 of the 2,000 constructed splitting cases are true equations; this is a subcount, not an extra contribution to the total. The script also checks Bell numbers through index 6.

These are finite formal-group-algebra and coordinate checks. They are not actual surreal exponential evaluations, a full quantifier-elimination implementation, a proof of the Turing-degree statement, or a formal proof of the infinite/class-sized claims. No Lean code was compiled or supplied.

## 6. Document verification

The final source was compiled with `latexmk` and `pdflatex`. The final LaTeX log had no unresolved references, overfull boxes, or underfull boxes. All 28 pages were rendered for inspection, and selected pages were examined at readable resolution, including the title, toric/constant-field proofs, the single-slope computability proofs, and the audit table. This checks presentation, not mathematical correctness.

The delivered archive excludes intermediate LaTeX files, downloaded third-party papers, rendered inspection images, and font files. Its PDF, source, code, recorded output, and audit notes are all included explicitly.
