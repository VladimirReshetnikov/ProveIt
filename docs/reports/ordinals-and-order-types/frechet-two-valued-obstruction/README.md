# A two-valued obstruction to gluing Fréchet powers

**A proposed solution of Massas's sheaf question**  
Research manuscript, 20 September 2026. The PDF has 20 pages.

## Result

For a set A, consider the presheaf F ↦ A^ω/~F on all proper filters on ω
containing the cofinite filter, with arrows from stronger to weaker filters
and the dense Grothendieck topology. The manuscript proves in classical ZF:

> This presheaf is a sheaf if and only if A has at most one element.

The counterexample is an explicit matching family of constant sections
using just two values. Its covering sieve has countably many generators;
each generating filter has a countable base. The distinction between the
number of sieve generators and the size of the full sieve is essential.

The documented question is in Guillaume Massas, *A Semi-Constructive
Approach to the Hyperreal Line* (2023), p. 517 after Fact 5.10. It is repeated
in his 2024 dissertation *Duality and Infinity*, p. 249 after Fact 7.4.10.
See `literature_search.md` for precise references and the status limits.

## Additional proved results

- Separatedness and finite pasting in ZF. A finite number of sieve generators
  cannot witness failure, whereas a countable number can.
- Failure above every countably generated proper free filter, also in ZF;
  the obstruction survives restriction to the countably generated site.
- In ZF + dependent choice, for a nontrivial A, sheafness above a fixed
  filter F is equivalent to finiteness of P(ω)/I_F, where
  I_F = {S : ω\S belongs to F}. The finite direction uses ZF alone.
- In ZFC, the associated sheaf is the product, over ultrafilters U extending
  F, of the ultrapowers A^ω/U. The binary obstruction becomes a missing
  characteristic-function section.

## Contents

| File | Purpose |
| --- | --- |
| `article.pdf` | Complete 20-page article |
| `article.tex` | Self-contained LaTeX source, including bibliography |
| `references.bib` | Reusable bibliographic database; not needed by the build |
| `obstruction_witness.py` | Exact integer certificate from alleged cofinite cutoffs |
| `verify.py` | Supplementary arithmetic and finite-pasting checks |
| `verification_results.json` | Actual deterministic output of those checks |
| `proof_audit.md` | Definitions, quantifiers, dependencies, and boundary-case audit |
| `literature_search.md` | Sources, exact locations, and limitations of the novelty search |
| `build.sh` | Clean PDF build using three pdfLaTeX passes |
| `build_environment.txt` | Tool versions used to generate the delivered files |
| `qa_report.json` | Build, rendering, and reproducibility checks |

## Rebuild the PDF

A TeX distribution with pdfLaTeX and the packages named in `article.tex` is
required. The fonts come from the distribution's `newtx` packages; font files
are not included. Run:

```sh
bash build.sh
```

Alternatively, run `pdflatex -interaction=nonstopmode -halt-on-error article.tex`
three times. The bibliography is included in the source, so BibTeX is not
needed. The delivered PDF was built with no undefined references, overfull
boxes, or other LaTeX warnings on the final pass.

## Reproduce the exact checks

Python 3.9 or later is sufficient; there are no third-party dependencies.

```sh
python3 verify.py --output verification_results.json
python3 obstruction_witness.py 3 100 150
```

The second command returns the contradictory index 151. The first checks
150,000 row–tail identities, 64,925 cutoff certificates, and 86,669 finite
local configurations, including 9,209 compatible configurations. It also
checks invalid input handling. The fixed random seed is 20260920.

**Scope of computation:** these tests are not a proof of the infinite
classification and are not a proof-assistant formalization. The finite
pasting tests use arbitrary proper filters on finite index sets, not
cofinite-extending filters. There are no proper cofinite-extending filters
on a finite index set. The complete infinite proof is in the article.

## Research status

The manuscript was prepared with ChatGPT in response to a request to attack
an open problem. It presents complete proofs but has not been independently
refereed or checked in a proof assistant. No later resolution was found in a
targeted search as of 20 September 2026; that is not evidence that every
publication or unpublished argument has been excluded. Priority and novelty
are not certified. The source author was not contacted, and nothing was
submitted or published on the user's behalf.

The primary result is an asserted mathematical solution of the cited
question, not merely a proposed strategy; its public status remains that of
an unrefereed manuscript.
