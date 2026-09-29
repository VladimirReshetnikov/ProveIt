# Sparse Computable Erasures and Least-Degree Obstructions

**Low counterexamples, finite meets, and descending chains in effective-dense equivalence classes**

Research draft prepared for Vladimir Reshetnikov, 28 September 2026.

## Main result

The article supplies a negative answer to ProveIt's question C2, the
effective-dense instance of Peter M. Gerdes's Question 7, for both uniform
and nonuniform reducibility. A binary 1-generic set that computes no
function eventually different from every computable function has no
least ordinary Turing-degree representative in either equivalence class.
This includes every 2-generic and every non-high 1-generic. In particular,
the counterexample can be low and computable from the halting set.

The erasure construction remains inside the **uniform** equivalence class,
even when defeating proposed least representatives from the **full
nonuniform** class. It uses computable masks, explicit omission outputs,
and error-free description transformations; it does not transfer a coarse
counterexample by treating errors as omissions.

Additional results include arbitrary unbounded computable every-prefix
budgets; exact ordinary-degree order, joins, and meets for computable masks;
finite and uniformly presented countable simultaneous avoidance; finite
Boolean degree patterns; and a strictly descending chain of representatives
within one uniform class with no lower bound belonging to the nonuniform
class. The starting set and every member of that chain can be low.

## Files

- `article.pdf`: final article, including complete conventional proofs,
  twelve further research questions, source provenance, and a proof checklist.
- `article.tex`: standalone LaTeX source with an embedded bibliography.
- `build.sh`: runs the finite checks and compiles the PDF.
- `PROOF_AUDIT.md`: dependency and quantifier audit.
- `SOURCES.md`: pinned repository and primary literature ledger.
- `REPOSITORY_UPDATE.md`: a suggested C2 status update for review; it has not
  been applied to the repository.
- `checks/check_finite.py`: deterministic Python checks of finite invariants.
- `checks/results.json` and `checks/run.txt`: recorded successful test output.
- `SHA256SUMS`: content hashes of the release files other than itself.

## Build

With Python 3.10+ and a standard TeX Live or MiKTeX installation:

```sh
bash build.sh
```

The TeX packages used are ordinary packages distributed with those systems:
Latin Modern, AMS math, geometry, microtype, booktabs, longtable, xcolor,
enumitem, fancyhdr, titlesec, xurl, hyperref, and bookmark. No BibTeX or
network access is required.

Alternatively, run the following from this directory; repeat pdfLaTeX until
cross-references settle:

```sh
python checks/check_finite.py
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

## Mathematical and verification status

The article presents conventional proofs, not a conjectural outline.
It has not been independently refereed or formalized in Lean. The
2-generic route is proved directly. The low refinement explicitly uses the
published high-or-DNR characterization of Kjos-Hanssen, Merkle, and Stephan
(Theorem 5.1), in addition to genericity facts proved in the article.

The literature search was targeted. The relationship to the repository
question and the cited published formulation was checked, but independent
priority or novelty has not been established. Standard genericity and
highness results are identified as classical, not claimed as discoveries.

The finite checks validate coordinate and counting invariants only. They
cannot establish genericity, verify an infinite density limit, or certify
the least-degree theorem. The script does not simulate a noncomputable
oracle or enumerate all total computable functions.

The conclusions do not settle the high 1-generic case, the existence of
minimal elements in the full equivalence class, or arbitrary countable
coinitiality. These distinctions are explicit in the article.

## Repository anchor

`VladimirReshetnikov/ProveIt`, commit:

`1a1396d4d3a2ac6812692df520517d86ba3a4785`

Primary target:

`Computability/TuringDegrees/Research/CoarseDegrees/research-plan/turing_degrees_unified.tex`

The repository was read, not modified.
