# Source and claim audit

## Repository pin

Repository: https://github.com/VladimirReshetnikov/Surreal

Inspected commit: `465a54b479a1ee842cbf7db1689a7d2f6bfe25e1`.

The repository tree, root README, documentation index, trigonometry README and
LaTeX source, and surcomplex-field-automorphisms README were accessed through
the GitHub connector. The relevant source text was read/searched; this was
not a checkout, a repository build, or an exhaustive review of every report.

The pre-existing trigonometry material includes finite-angle uniformization,
all global phase extensions, unavoidable individual infinite periods, and the
local phase law. These are credited in the article, not claimed as new.

The automorphism guide already identifies fixed-shift flows (Theorem 5.2),
including the parameter-sign variant of t -> t/(1+ct). The article claims an
application to phase stabilizers, not priority for those flows.

## Primary literature

1. Philip Ehrlich and Elliot Kaplan, *Surreal ordered exponential fields*,
   Journal of Symbolic Logic 86(3) (2021), 1066–1115,
   DOI 10.1017/jsl.2021.59.
   https://arxiv.org/abs/2002.07739v3
   Relevant: Sections 5 and 11, especially the first open question in 11.1.
   The v3 PDF pages 33–34 were inspected as images as well as parsed text.
   The strip formula on page 33 swaps sine and cosine; the article explicitly
   uses the intended cos + i sin convention, consistent with the immediately
   following global formula and the asserted group-homomorphism property.

2. Emil Jeřábek, *Rigid models of Presburger arithmetic*, Mathematical Logic
   Quarterly 65(1) (2019), 108–115, DOI 10.1002/malq.201800019.
   https://arxiv.org/abs/1803.05797
   Relevant: Sections 2–4, canonical residue maps, the divisible kernel, and
   reduced/Leibnizian Z-groups. These abstract group facts are classical and
   explicitly acknowledged as such.

3. Elliot Kaplan, Lothar Sebastian Krapp, and Michele Serra, *Decomposing the
   automorphism group of the surreal numbers*, arXiv:2509.22374v3,
   April 23, 2026.
   https://arxiv.org/abs/2509.22374v3
   Relevant: class conventions and Section 4 on strongly linear automorphisms.
   The constructed translations are not asserted to preserve Gonshor exp.

Conway's and Gonshor's standard books are cited for background normal-form and
surreal analytic machinery. They were not newly read in full for this task.

## Proposed contributions and limits

The central proposed construction is the two-vector avoidance recursion that
minimizes the multiplier ring while preserving an arbitrary ordinary phase
character and therefore the profinite defect. Both the set-sized and class
versions are proved, and their assumptions are separated.

The application to Ehrlich–Kaplan is a specific negative conclusion: initiality
of the kernel-multiplier ring, even with the stated local identities and
pointwise residue-phase agreement, is insufficient. It does not assert that
Ehrlich and Kaplan conjectured initiality alone was enough. It does not settle
their separate comparison problem for exponentials from different initial
embeddings, or classify all possible sufficient hypotheses.

The profinite phase realization, cofinal divisible-period consequence for No,
and free translation action are additional proposed results/applications.
Classical Z-group residue theory, canonical integer-part exponentiation, and
the repository's phase classification are not claimed as new.

The search found no prior statement of the principal minimal-multiplier
construction in the inspected material. That is not a proof of historical
priority. No formal proof assistant has checked the manuscript. The finite
Python checks support examples and displayed finite identities only.
