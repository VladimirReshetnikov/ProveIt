# Exponential Relations over Omnific Integers

**Exact toric kernels, decidable fragments, and one-scale elementary cores**  
Research manuscript, 23 September 2026.

## Contents

- `article.pdf`: the complete 28-page typeset article.
- `article.tex`: self-contained LaTeX source, including its bibliography.
- `SOURCE_AUDIT.md`: source provenance, claim classifications, dependency and limitation checks.
- `code/checks.py`: exact finite checks and a reusable balanced-partition generator.
- `check_results.json`: the actual deterministic test result, with 22,074 cases passing.
- `Makefile`: build and check commands.
- `MANIFEST.sha256`: checksums of the delivered files other than the manifest itself.

No external bibliography database, image assets, proprietary software, or network connection is needed to build the article or run the checks. A normal LaTeX installation must provide the packages listed in `article.tex`.

## Mathematical scope

Write `Oz = Z + J`, where `J` is the real vector space of purely infinite surreal normal forms. Let `A` be the field of real algebraic numbers. The manuscript develops the following results.

1. **Faithful exponential group algebras and exact relations.** On the additive domain `Qbar + J` in `No[i]`, use the ordinary complex exponential for the algebraic constant part and Gonshor's exponential for the purely infinite part. Distinct arguments have exponentials linearly independent over `Qbar`. Consequently, the finite polynomial relations among these exponentials are exactly their additive toric relations. The ordinary constants in every finitely generated such field are determined exactly.

2. **A decidable exponential-equality language.** Start with ordered additive omnific arithmetic. Add externally interpreted zero predicates for finite exponential sums with algebraic coefficients, complex-algebraic shifts, and real-algebraic affine slopes. The entire first-order theory in this precise language is decidable. The proof first uses balanced partitions, then separates ordinary integer coordinates from purely infinite coordinates, and finally eliminates quantifiers in Presburger arithmetic and ordered algebraic vector spaces.

3. **Definability, elementary substructures, and embeddings.** In that language, the integer part and purely infinite part are definable. Every definable set is a finite union of integer/vector rectangles. The elementary substructures inside `Oz` are exactly `Z + W` for nonzero ordered `A`-vector subspaces `W` of `J`. Thus `Z + A*u` is a countable elementary core for each positive purely infinite `u`. These are additive relational structures, not subfields and generally not subrings.

4. **An exact computability boundary.** For a fixed irrational real `alpha`, use just addition, order, `0`, `1`, and the relation `S(x,y)` meaning `exp(y)=exp(alpha*x)`. Its first-order theory has exactly the Turing degree of the rational cut of `alpha`. It is therefore decidable precisely when `alpha` is a computable real. This is a fixed-parameter statement; uniform decision from arbitrary approximation programs fails even with algebraic irrational slopes promised.

5. **Limits and further consequences.** Adding `exp(x*y)=exp(z)` to the decidable algebraic language makes the full first-order theory undecidable. Explicit counterexamples locate the failure of independence when arbitrary finite constants or infinitesimal tails are admitted. For arbitrary positive real bases, a separate theorem determines the purely infinite fibers above ordinary integer solutions of equations such as `a^x+b^y=c^z`.

Section 14 proposes eleven further research topics. The introduction, Appendix A, and `SOURCE_AUDIT.md` distinguish classical inputs, elementary transports, proposed contributions, and unresolved extensions.

## Status and limitations

This is an AI-assisted, unrefereed research manuscript. Its arguments are supplied in full relative to the explicitly cited classical inputs. The results are proposed contributions, not certified priority claims or a claimed settlement of a named classical conjecture. A bounded literature and repository search cannot establish that a statement has never appeared before.

The article does **not** claim decidability of the unrestricted surreal exponential field, an internal exponential operation on `Oz`, a global surcomplex exponential, a decision procedure for arbitrary surreal normal forms, or an implementation of the full decision procedure. It does not define exponential values at infinitely large imaginary arguments.

The finite tests validate exact combinatorial and coordinate identities. They do not prove Gonshor's theorem, Lindemann--Weierstrass, quantifier elimination, the Turing-degree result, or proper-class claims. No Lean verification or external peer review was performed.

## Reproduce the PDF

Using a standard TeX Live or equivalent installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `pdflatex` three times to stabilize the contents and cross-references:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The PDF was built successfully with no overfull/underfull box warnings or unresolved references in the final log. All pages were rendered and visually inspected, with selected mathematical pages inspected at higher resolution. Binary PDF bytes can vary between TeX versions or builds; the mathematical source and test output are the reproducible inputs.

## Run the exact checks

Python 3.10 or newer; standard library only:

```sh
python3 code/checks.py --output check_results.json
```

The expected headline is `"status": "PASS"`, with `"total_cases": 22074` and seed `20260923`. A failure raises an exception, including when Python optimization is enabled. The script's size cap for direct partition enumeration is deliberate; Bell-number growth makes this a small exact prototype, not a scalable solver.

## Repository comparison

The comparison used the following immutable snapshot:

```text
VladimirReshetnikov/Surreal
958b5c4865819bd55ea1f5ffc050282aea7ef570
```

The inspected material was the report catalogue and selected relevant material on omnific quotients and exponential automorphism rigidity. The whole repository was not audited. None of its conjectural or unreviewed mathematical claims is used as a theorem in the present proofs. The source audit records this boundary in detail.
