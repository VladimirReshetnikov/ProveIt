# Independent replay: universal syntax of the candidate PRA presentation

`UniversalPrefix` recognizes a finite chain of universal quantifiers followed
by an open matrix. Lean proves each axiom in the explicitly constructed
`UniversalAxiom` family has this form, including equality congruence and the
parameterized characteristic and search schemas. Together with the previously
reviewed sentence-level equivalence,
`candidate_has_universal_presentation` establishes existence of an explicitly
defined, deductively equivalent universal presentation for the candidate PRA
theory. It does not establish effective axiom recognition, equivalence with
standard PRA, witnessing or Π₂ conservation.

Two separate builds against the independent equivalence provider
`/tmp/pra-universal-independent-m5hxtn5a/lib` passed all four modules. Their
source, object and complete-log hashes match. The driver checks all 44 parent
source and object hashes and the frozen syntax sources. [Independent driver,
state and logs](pra-universal-syntax-root-replay/) and the [author packet](pra-universal-syntax-author-replay/)
are preserved. Historical failed probes, including admitted scratch code, are
labeled as such and are not compiled or imported. Foundation, Mathlib and
unchanged local objects remain inherited cache boundaries.
