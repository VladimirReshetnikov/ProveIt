# Independent cyclic-basis audit

The audit passed with **zero decision, certificate, compiler, or corruption
discrepancies**. The final recorded run used seed `20261012` and took **6.514
seconds** in the supplied workspace. This is a finite correctness audit, not an
asymptotic benchmark or a test of the topological marking layer.

## Reproduction

From the workspace containing `ProveIt` and `experiments_basis`:

```sh
python experiments_basis/audit_cyclic_basis.py
```

For a different checkout location:

```sh
python audit_cyclic_basis.py --fast-path /absolute/path/to/ProveIt/Topology/UnknotRecognition/fast --output audit_results.json
```

The script's standard output and `audit_results.json` record the exact finite
bounds, random seed, coverage, exceptions, source hashes, and any counterexample.
It also checks that the production source files did not change during the run.

## Independent decision oracle

Words use the signed alphabet `(-2, -1, 1, 2)`. Free reduction uses a literal
stack. Cyclic reduction strips inverse end letters after that reduction. The
oracle enumerates all 16 type-II Whitehead characteristic pairs in rank two,
applies each map to every tuple entry, and repeatedly takes a strict decrease in
the total cyclic length. It accepts exactly when the resulting entries are
distinct one-letter conjugacy classes. Whitehead's descent theorem for cyclic
tuples justifies the terminal criterion.

The oracle does not call the production Euclidean selector, homology functions,
SLP compiler, `WordArena`, or certificate verifier. In particular, its decision
does not use determinant tests. A cache identifies cyclic rotation, independent
inversion, and permutation of tuple entries; every indicated literal input is
still sent separately to the production implementation.

The classical tuple minimization background is Roig, Ventura, and Weil, *On the
complexity of the Whitehead minimization problem*, International Journal of
Algebra and Computation 17 (2007), 1611–1634,
<https://arxiv.org/abs/math/0608779>. Enumerating all moves is appropriate for this
small fixed-rank audit, rather than an implementation claim for variable rank.

| Decision family | Cases | Positive cases |
|---|---:|---:|
| Every nonempty cyclically reduced word of length at most 6 | 1,104 | 196 |
| Every ordered pair of nonempty cyclically reduced words with total length at most 6 | 6,576 | 648 |
| Unstructured random literal singleton/pair inputs | 400 | 41 |
| Random automorphism images, independently inverted and conjugated | 397 | 397 |
| Named boundary and counterexample controls | 9 | 2 |
| **Total** | **8,486** | **1,284** |

All 1,284 emitted positive certificates also passed the production verifier and
a second replay using independent literal substitutions in chronological order.
The latter independently checked the final oriented target letters after cyclic
reduction.

There were 400 attempts to generate random positive cases. Three attempts were
discarded before testing because the explicit generation cap was exceeded. They
are recorded separately, rather than counted as passing tests.

## Nielsen compiler audit

Two fixed sequences explicitly use noncommuting moves. A further 400 random
sequences use ranks 2 through 5 with nonconsecutive generator labels. Six random
generation attempts exceeded the explicit audit cap before testing.

The remaining **396 sequences** produced **4,008 literal-word comparisons**.
For each sequence, the audit compared the backwards shared-grammar compiler
with direct forward substitutions, including the entire unreduced output. It
then applied the inverse sequence and checked all 4,008 roundtrips by literal
free reduction. Every comparison passed.

The tested sequences contained 508 inversions, 506 swaps, and 1,532 powered
multiplications. Those multiplications included 768 left-sided and 764
right-sided moves, 744 negative and 788 positive powers, and 1,226 powers with
absolute exponent greater than one. The maximum sequence length was 14; the
largest checked unreduced output had 36,687 letters.

## Corruption and alphabet checks

The mutation audit used three rank-two certificates and a supplied rank-three
certificate. **All 71 malformed-schema mutations were rejected**, including
Boolean and floating-point certificate alphabets, Boolean targets and move
parameters, invalid sides, self-multiplications, zero powers, missing fields,
and extra fields.

There were also **24 syntactically valid changes** to moves, targets, or input
words. Independent forward substitution found 20 invalid proofs and 4 proofs
that remained valid; the verifier agreed in all 24 cases. Acceptance of a
changed but still mathematically valid proof is intended. For example, changing
a rank-two shear from left multiplication to right multiplication preserves its
action on conjugacy classes.

The producer rejected each undeclared-alphabet input `[3]`, `[3, 1, -3]`, and
`[3, -3, 1]` with `ValueError`, so cancellation cannot conceal an undeclared
source letter.

## Sharp controls

Write `[a,b] = a b a^{-1} b^{-1}`.

* `(a, a b^2)` has two individually primitive entries but determinant 2, and is
  not jointly primitive.
* `(a, a)` has two individually primitive entries but determinant 0.
* `(a[a,b], b)` has determinant 1 but its first entry is nonprimitive.
* `(a[a,b], b[b,a])` has determinant 1 but both entries are nonprimitive.
  Each entry is cyclically reduced of length 5 with the corresponding unit
  exponent-sum vector.
* `(b a b^{-1}, a b a^{-1})` is jointly primitive as an ordered pair of conjugacy
  classes and is accepted. Independent conjugations are intentional.
* Empty and freely trivial classes are rejected. Three classes in rank two are
  rejected. The empty tuple is accepted.

The determinant-one nonprimitive controls show why homology alone does not
decide the problem. Both cyclic images under the selected common lift must be
checked.

## Scope and interpretation

The rank-two common-lift criterion is a correct direct consequence of the
classical isomorphism `Out(F_2) = GL(2,Z)`: a primitive conjugacy class with a
specified primitive exponent-sum vector is unique. A unimodular pair of vectors
therefore selects one automorphism under which a jointly primitive ordered pair
must become the two target conjugacy classes. Both resulting cyclic reductions
must still be tested. Kapovich's Proposition 8.1 and Corollary 8.2 state the
needed uniqueness precisely: <https://arxiv.org/html/2607.21499v1>.

This criterion concerns independently conjugated boundary classes. It must not
be advertised as a test that the supplied based words themselves form a free
basis. Its support-block extension is complete when every connected component
of the cyclically reduced support graph has size at most two. Refusal on a
larger block is not evidence of nonprimitivity.

Application to primitive boundary multicurves still requires separately
authenticated disjoint embeddings and correct handlebody markings. The audit
does not test that layer, a hierarchy construction, or a knot-recognition
complexity bound. The novelty claim should concern this precise application,
certificate organization, implementation, and measured terminal improvement;
rank-two primitive-class uniqueness and primitive-multicurve topology are
classical inputs.

## Frozen source hashes

| Source | SHA-256 |
|---|---|
| `audit_cyclic_basis.py` | `3a796975451266878932a0fe2c756b4d9c2cb5aa8509c9690a193b13f2cc872a` |
| `cyclic_basis.py` | `c1777bd14854b3aa3af9c6183726bb91f9c8b0afa8f5737797f45d956aeba91a` |
| `cyclic_basis_verify.py` | `49cd9b135453dcc9e3f53145e397967874d1555cc4eaab1850cd5c16ce857fa5` |
| `compressed_words.py` | `55daf4a565d4b2683f2a808db68a8c20ca73d31922a5abe375ff0beec4555fa2` |
