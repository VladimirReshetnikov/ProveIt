# Claim and verification status

Date: 20 September 2026.

## Target

Athanasiadis–Chapoton, arXiv:2605.26916v1, Question 4.6 (p. 13): determine
ordinary shellability and Cohen–Macaulayness of the lattice-point poset for an
arbitrary finite preorder, beyond the maximum-vertex case established there.

## What this package claims

A complete proposed affirmative proof, with no conjectural step used as an input.
The abstract theorem applies to equidegree base families satisfying specified
insertion exchange. Every integral-polymatroid integer independence poset
satisfies that condition. The preorder application is established separately by
labeled supply assignments and alternating-path rerouting.

The critical statement is the exact old-face intersection identity in Theorem
4.3, not the finite output. The preceding overlap lemma and word-completion
lemma prove it. The terminal-ridge term is essential.

Additional proved statements concern restriction faces, ordinary and flag
h-polynomials, all rank selections, and contractibility of the unweighted
nonempty preorder complex after removing its minimum. The latter complex need
not be a ball; a three-element universal preorder gives an explicit example.
The empty preorder is handled separately and its empty-face complex is not
claimed to have a contractible geometric realization.

## What was actually run

`python3 code/verify.py --output results`, with default maximum size four,
completed successfully. Full totals are in `results/verification.json`.
All tests use integers and finite sets; there is no numerical approximation,
random sampling, recurrence guessing, or inference from an OEIS match.
The included PDF was built from the included source with pdfLaTeX and inspected
as rendered page images. No proof assistant was run.

The tests exhaust the labeled preorders through size four, all nonempty
three-coordinate equidegree base families in ranks one through three before
filtering by exchange, and the two declared capacities on every three-element
preorder. They do not exhaust larger ranks, arbitrary submodular functions,
or size-five preorders. They do not independently calculate every link's
integral homology: that conclusion follows from the shelling proof.

## Literature and novelty boundary

The selected question is explicitly posed in the retrieved primary paper.
Targeted title/question/shellability searches and inspection of the cited later
preorder-support paper did not locate a solution. This is a report of the search,
not a guarantee of global novelty or of unpublished status.

Polymatroid exchange, the algebraic background, standard word shellings of a
single product of chains, and the homological consequences of shellability are
classical. They are proved or credited. The general base-overlap construction
may have antecedents under different terminology. The article supplies the
whole ordinary simplicial shelling argument rather than relying on a claim
that an M-shelling of a monomial ideal automatically supplies it.

No theorem from the attached manifest's research packages is used. Those
packages were not independently reviewed in this work. Their catalogue entries
only guided problem selection and nonduplication.

## Explicitly not claimed

An independently refereed theorem; a proof-assistant certificate; priority for
all general lemmas; an EL-labeling; an efficient listing when exponentially many
facets exist; a ball/manifold model in general; real-rootedness or gamma-positivity;
the full q-refined reciprocity question; or the manifest's flag-polytope problem.

The optional Ehrhart h*-interpretation imports the source's Ehrhart–Zeta
duality. It is separated from the construction and is not an input to it.
