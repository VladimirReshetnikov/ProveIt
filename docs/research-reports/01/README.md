# Coarse Classes Without a Least Turing Degree

Research note prepared for Vladimir Reshetnikov, 18 September 2026.

## Result

The manuscript attacks C1 in the supplied survey: must every nonuniform coarse
class contain a representative of least Turing degree?

The answer to the displayed question is negative. Every 1-generic binary set
has a uniform and a nonuniform coarse class without a least Turing degree,
even when arbitrary total numerical functions are allowed as representatives.

An important attribution qualification: this basic negative answer already
follows from Hirschfeldt–Jockusch–Kuyper–Schupp, *Coarse Reducibility and
Algorithmic Randomness*, Theorem 4.2 (preprint 2015, journal publication 2016).
It is not presented here as a new historical discovery.

The research attempt develops a stronger exact-pair statement. For any binary
X, let K_X be its binary density-zero description class and I_X the sets
computable from every member of K_X. For every prescribed P in K_X there is
D in K_X such that the common Turing lower information of P and D is exactly
I_X. Successful D's form a comeager set in the complete prefix-density
metric. For a 1-generic X, this gives a nonzero Turing minimal pair inside one
density-zero class, and a countable pairwise minimal-pair family.

The manuscript provides complete conventional proofs. The novelty of the
stronger formulation and the topological proof has not been established.
No independent expert review or proof-assistant verification is claimed.

## Files

- `paper.tex`: self-contained LaTeX manuscript; bibliography is embedded.
- `paper.pdf`: compiled 14-page report, with Latin Modern fonts and the input
  survey's navy/ink/pale color scheme.
- `build.sh`: rebuilds the manuscript using latexmk and pdfLaTeX.
- `checks/check_finite_geometry.py`: deterministic exact-arithmetic tests.
- `checks/results.json`: actual output of those tests.
- `proof_audit.md`: quantifier, effectivity, topology, and attribution audit.
- `sources.json`: precise source versions, relevant statements, and audit limits.
- `validation.json`: build, layout, and test status.
- `input/turing_degrees_unified.tex`: unmodified supplied survey for provenance.

No third-party research papers, font binaries, or LaTeX intermediate files are
bundled. The input survey is preserved as supplied; its other claims were not
re-audited by this project.

## Rebuild

Install a LaTeX distribution containing pdfLaTeX, latexmk, Latin Modern, and the
packages named in the preamble. From this directory, run:

```sh
sh build.sh
```

The script writes temporary LaTeX files under `build/` and copies the completed
PDF to `paper.pdf`. It does not require shell escape, downloads, a separate
bibliography processor, or private font files.

Run the finite regression tests with Python 3.10 or newer:

```sh
python3 checks/check_finite_geometry.py
```

Only the Python standard library is used. To retain the supplied test output,
choose a different result path:

```sh
python3 checks/check_finite_geometry.py --output /tmp/coarse_checks.json
```

## Verification scope

The tests check 299,592 finite triangle inequalities, 12,456 local completion
instances, 7,736 finite patches, and further finite metric, sparse-coding, and
majority-count identities. These are regression tests, not a proof of any
infinite Turing-degree claim. There is no executable halting oracle, no finite
simulation certified as 1-generic, and no claim that the constructed exact
partner is computable or computable from the halting set.

The complete proof dependency chain appears in Section 9.2. The most important
new-to-this-manuscript argument to review is the local decoder in Lemma 4.1 and
its use in the cone dichotomy and exact-pair theorem.
