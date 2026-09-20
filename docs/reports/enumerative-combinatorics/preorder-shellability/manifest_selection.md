# Manifest selection and nonduplication record

Input: the user-attached `manifest.tex`, dated 20 September 2026, cataloguing
71 research packages. SHA-256 of the exact supplied file:

`729fb6e3aef3f30c7c5284c4296681fba72b6d6af68211f178ad0bc3c5d15b41`

The complete manifest was read for selection. The references below are line
numbers in the original plain-text file (not the separate retrieval tool's
line-numbered presentation).

## Closest listed report: reciprocity and matrix duality

Title: **Reciprocity and Matrix Duality for Preorder Polytopes**.

Directory: `enumerative-combinatorics/preorder-polytope-reciprocity`.
Original source archive named by the manifest: `preorder_reciprocity.zip`.
Original file lines 960–969.

The catalogue attributes solutions of Conjectures 7.2, 4.2, and 4.4 and the
ordinary q=1 part of Conjecture 4.9 in Athanasiadis–Chapoton to that report.
Its described methods concern Ehrhart–Macdonald reciprocity and bipartite
matrix duality. Those targets are not Question 4.6.

## Other closely related listed report: preorder support polynomials

Title: **A Reflexive Root-Polytope Model for Preorder h-Polynomials**.

Directory: `enumerative-combinatorics/preorder-root-polytopes`.
Original source archive named by the manifest: `preorder_root_polytopes.zip`.
Original file lines 981–994.

The catalogue attributes a polyhedral realization and the palindromicity and
unimodality conclusions in Conjecture 5.1 to that report. It describes the
support enumerator and credits a later paper for a related duality. It does not
claim ordinary shellability of the lattice-point poset or an answer to 4.6.

## Selected distinct target

Question 4.6 of the same primary paper asks for ordinary shellability and
Cohen–Macaulayness of Pτ for arbitrary finite preorders. This package addresses
that topological question, using base exchange and compatible shellings of
principal coordinate boxes. It does not repackage the two catalogue entries'
enumerative claims as a new result.

The chain-complex h-polynomial derived from the new shelling is generally
**different** from the support enumerator. For the three-element preorder with
1<2 and 1<3, the article computes them as 1+8z+3z² and 1+5z+5z²+z³ respectively.

## Scope of the comparison

The nonduplication comparison is grounded in the complete catalogue, not in
unseen contents of the underlying report archives. No underlying archive was
needed or reviewed, and no proof from one is used. The manifest explicitly
states that its descriptions record claims and that the catalogue did not
check those proofs; this package does not silently upgrade that status.
