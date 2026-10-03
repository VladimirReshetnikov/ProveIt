# Research status

This is an AI-assisted mathematical research manuscript. Its main
statements are supplied with ordinary proofs, not merely conjectured.
They are not claimed to be independently refereed, historically first,
or verified by a proof-assistant kernel.

## Proof scope

The global homogeneity theorem is formulated in GBC with a fixed baseline
class enumeration. Input class-word families must be uniform and indexed
by a set. Every stage of the back-and-forth is a set partial map of set
codes. No elementary transfinite recursion principle with class-sized
stage values is invoked.

The regular set theorem assumes an infinite regular kappa with
kappa^(<kappa) = kappa and a kappa-sized ordered alphabet filling all
cuts of total size less than kappa. Singular lengths are not included;
the manuscript proves a cofinal profile obstruction and explains the
difference between bounded and small support there.

The main non-invariance assertion concerns a precise reduct retaining
the core order and prefix cylinders but forgetting coordinate labels and
cross-node label equality. It does not make exhaustiveness undefinable
in the fully labelled ambient set theory.

The group-cardinality result is a set-sized theorem. Notation for all
class branches and class automorphisms in GBC is virtual, not a claim
that a same-level class of classes exists.

## Checks actually performed

The supplied standard-library Python script passed 269,329 assertions,
covering finite ordered prefix profiles, maximum-attained one-point
extension in both directions, prefix equivalence, finite supported
completion, and a label-coherence counterexample. It does not test the
limit-prefix case, proper-class recursion, global homogeneity,
exhaustiveness, cardinal arithmetic, or Lean correctness.

The PDF was compiled from the supplied LaTeX source and its layout
inspected in rendered pages. The repository's Lean interfaces were read,
but the repository was not built and no new Lean module was delivered.

## Attribution

The set-sized embedding spectrum, supported core, core density, unranked
prefix-height recovery, direct comparison of raw class orders, and
represented-cut extension criterion are earlier mechanisms, credited in
the article. The new continuation centers on configuration homogeneity,
parameter-robust invisible exhaustiveness, cylinder-preserving
nonextension, edge-coherent rigidity, and their set analogues.
