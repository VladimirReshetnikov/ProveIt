# Sources and scope

## Repository pin

Vladimir Reshetnikov, ProveIt, Adjacency-bounded 132-avoiders, combined article.
Commit: 7421a4ca60fdf125411edf412f825aac54278b37
Git blob: b9697af6c8489fb1e0b3670037a50aa70fdc6f80
Inspected: 1 October 2026
https://github.com/VladimirReshetnikov/ProveIt/blob/7421a4ca60fdf125411edf412f825aac54278b37/SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders/article.tex

Inherited facts: endpoint recurrence (prop:endpoint), uniform Catalan-triangle
coefficient bound (crem:lem:uniform-tail), scalar-root expansion
(crem:thm:main-allorders), and spectral corridor
(crem:thm:corridor-quantitative). The source's joint-growth question appears
in Part II, Joint growth of length and adjacency bound.

## Previous companion

A Uniform Logarithmic Bridge for Adjacency-Bounded 132-Avoiders, research
note prepared for Vladimir Reshetnikov with OpenAI, 1 October 2026.
Package: Uniform_132_Avoider_Spectral_Bridge_Package.zip
This supplies the squared coefficient majorant and the clustered Fourier
method at logarithmic precision. The new proof re-establishes all uniform
estimates needed for the relative equivalent, sums the cluster count, and
uses an exact retained subclass to prove relative tightness.

## Credited implementation

checks/model.py is byte-identical to the endpoint/Catalan model from the
repository's polynomial-rarity work, Git blob
a4fdee376119a24c057623829b76cee71628b369. Its SHA-256 is
c693d80529b69762600edc4b4d271155e6aa12c9127bda9a59a839ee143538f7.
It credits the Mayama-Akita recurrence and the repository's earlier
05-model implementation, Git blob f0248e0d6181200257e2949c1a8fa8f9fecf5617.
The present primary grammar verifier and independent replay are separate
additions. The independent replay imports no code from model.py.

## Public primary enumeration references

N. Nadler, On 132-avoiding permutations with an adjacency constraint,
arXiv:2604.22135v1 (2026): https://arxiv.org/abs/2604.22135

T. Mayama and D. Akita, Finite-state enumeration of adjacency-constrained
132-avoiding permutations, arXiv:2605.23519v1 (2026):
https://arxiv.org/abs/2605.23519

These records were inspected for enumeration context during the research.
The report makes a source-relative contribution, not an exhaustive worldwide
priority claim. No external paper is redistributed.
