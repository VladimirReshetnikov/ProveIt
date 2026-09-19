# Proof and attribution audit

This audit was performed during preparation of the manuscript. It is not an
independent review or a formal verification certificate.

## 1. Exact target and prior work

C1 is the universal least-representative assertion using nonuniform coarse
reducibility, as written in Gerdes Question 7 and in the input survey. A binary
counterexample suffices for the version allowing arbitrary numerical functions.
The basic negative answer follows from HJKS Theorem 4.2. It should not be
advertised as a newly discovered solution of a genuinely unresolved problem.

The exact-pair theorem and prefix-density/category argument have full proofs in
the manuscript. Their novelty is unverified; a search that fails to locate an
identical statement does not establish priority.

## 2. What “minimal pair” means

The constructed oracles are noncomputable, and every set below both is
computable. This is a Turing minimal pair. Neither individual degree is asserted
to be a minimal degree. The pair does not form a minimal pair of coarse degrees:
the two coarse degrees are equal and nonzero. No absence of minimal elements in
the Turing spectrum is asserted. The proved conclusion is absence of a least
one.

## 3. Correct topology

The limsup discrepancy delta is zero between all elements of K_X and cannot
support the proof. The metric actually used is the supremum of normalized
prefix discrepancies over every positive prefix length. The manuscript proves
that K_X is closed in the resulting complete metric space, and that finite
modifications of a fixed member form a countable dense subset.

Ordinary Cantor comeagerness of the collection of generic inputs is a separate
statement from relative comeagerness of exact partners in K_X.

## 4. Fixed-functional fibers are not assumed closed

The set of D for which Phi_e^D is total and equal to A need not be closed. The
argument applies nowhere density to its closure. Baire's theorem is invoked
only after closure, or after the implication that a countable cover by nowhere
dense sets is impossible. The simultaneous avoidance set contains a dense
G_delta; it is not asserted to itself be G_delta.

## 5. Local decoder

The decoding program searches finite strings tau and finite convergent
computations. It can test the rational prefix inequalities using its oracle Y.
It never queries the noncomputable ball center Z. Termination uses a correct
computation on a member of the dense fiber. Soundness completes tau by Z and
uses the strict 1/2 + 1/4 = 3/4 error budget. The completed oracle is inside the
ball, and its finite cylinder is relatively open, so density forces the output
to be the required bit.

All oracle computations on finite strings use only bits actually specified by
those strings. Strings and running times are dovetailed; divergence of an early
candidate never blocks the search.

## 6. Finite patches are nonuniform

A finite patch changes no Turing degree. The proof hardwires the actual finite
values and cutoff into the witnessing program. It does not extract those
values uniformly from a coarse-description oracle. The strict metric bound is
obtained using an intermediate eta' < eta; merely having each prefix value
less than eta would not alone imply a strict supremum bound.

## 7. Countability does not imply effective enumeration

There are countably many sets computed by P. The family of those not in I_X is
therefore countable, but there is no computable test for membership in this
family in the proof. The exact-pair construction is a classical nested-ball
existence argument, not an algorithm in P. No bound on the Turing degree of D is
claimed. Finite modifications of X may be used as centers even though the limit
avoids information computed by those centers; the metric limit does not
preserve Turing reductions.

## 8. Genericity lemmas

Finite product conditions and their interleaved coding are explicitly related.
Projection preserves 1-genericity; relative sections are justified by lifting
relative enumerations to ordinary c.e. pairs of finite conditions. The relative
meet proof uses a c.e. set of finite disagreements and the actual total outputs
to ensure termination. The contradiction does not assume uniform access to
avoidance prefixes.

Deleting a residue class changes at most density 1/k of a set, not density zero
for a fixed k. The robust-radius theorem is therefore essential before the
finite generic-intersection lemma is applied. Omitting that step would be a gap.

## 9. Numerical function representatives

Numerical coarse descriptions of a binary set are rounded without adding any
errors. A total numerical representative of a putative least degree is coded
by its graph, which is a set oracle of the same Turing degree. This closes the
possible loophole of a nonbinary representative lying below the two binary
counterexamples.

## 10. Equal spectra are not equal classes

The density-zero class, uniform coarse class, and nonuniform coarse class have
the same Turing spectra by sparse coding. Their actual elements or coarse
degrees are not thereby identified. The least-degree/coarsening criterion is
stated for nonuniform equivalence. No unsupported uniform coarsening conclusion
is drawn.

## 11. Scope exclusions

Nothing here settles the effective-dense analogue. Replacing a set on a
density-zero set preserves coarse-description families but can create incorrect
answers in an effective-dense description. The main transfer lemma therefore
fails for that setting.

No full classification of possible nonprincipal coarse spectra, no effective
complexity bound for exact partners, and no new literature-open status for the
suggested follow-on question is claimed.

## 12. Actual verification performed

The LaTeX compiles without undefined references, overfull boxes, or warnings in
the final log. All pages were rendered, and layout was inspected at montage
scale with key proof pages inspected at higher resolution. Finite metric and
coding tests passed using exact arithmetic. These checks do not substitute for
an independent mathematical review. No Lean, Isabelle, Coq, or other proof
assistant was run on the infinite theorems.
