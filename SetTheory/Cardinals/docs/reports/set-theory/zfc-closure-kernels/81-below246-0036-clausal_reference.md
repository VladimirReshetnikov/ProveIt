# Complete ground-clause reference for PSC

Batch 148 / closure-kernel source 17 (`5e5603303d`) supplies an ordinary
complete alternative to the defeated reduced numerical calculus. Its
`clausal_trace.py` is a reference specification with finite regression evidence,
not a measured small binary machine. The inherited `qpsc_syntax.py` constructs
actual equality-free subset-PSC axioms and universally closes parameters.
The PSC entry point accepts only matrices and a trace; generic logical test
formulas cannot be submitted as extra PSC axioms.

Signed clausification handles implication and quantifiers together. Each
universal occurrence receives a fresh variable; each existential occurrence
receives a globally fresh Skolem symbol depending on every universal in its
lexical scope. Environments handle shadowing without textual binder movement.
A permanent dummy constant makes the common ground-term domain nonempty.
Ground substitution checks exact symbol arities and assigns each distinct
clause variable a term; distinct variables may receive the same term.
This last feature enforces the cross-variable identifications missing from
the reduced engine.

The ground checker has two instructions: extend a branch by a source clause
with an explicit ground substitution, or close its newest literal against a
complementary ancestor. A stack restores every pending sibling branch.
Empty clauses close immediately; unfinished branches and trailing instructions
are rejected. Given a satisfying valuation, at least one child at every
extension preserves satisfaction, proving soundness. For a finite unsatisfiable
clause family, branch over its clauses and close at the first complementary
pair. This proves propositional completeness even with newest-literal closure.

The ordinary whole-search argument combines:

1. Every finite list of PSC instances is equisatisfiable with its generated
   Skolem clauses; symbols are fresh across the entire list.
2. Herbrand's theorem supplies a finite unsatisfiable ground family whenever
   that finite first-order theory is inconsistent.
3. The two-instruction checker accepts a finite trace for that family, and
   every accepted trace refutes only its reconstructed source axioms.
4. Decreasing-child natural codecs enumerate all finite matrix lists, ground
   terms and traces fairly. Invalid candidates are rejected individually.

Thus the *ideal finite-storage algorithm* has the intended PSC refutation
search contract. Together with the accepted ordinary PSC calibration, this
is an ordinary ZFC proof of its intended nonhalting/consistency equivalence.
It is not a kernel proof about CPython, a state bound, or a compiled table.
Host recursion/memory exhaustion is an execution error, never a refutation.
The complete wrapper, clausifier, term representation, trace checker,
enumerator and initializer must all be charged in a binary implementation.

Intake independently reviewed these unbounded arguments and reproduced the
finite suite: 159 formulas / 2,862 structure-expansion comparisons; all 20,854
clause families of at most four non-tautological clauses on three atoms,
including 4,613 refutations; 15 invalid traces; 200 actual PSC matrices;
5,000 round trips for each of three codecs; and explicit cross-variable and
diagonal specialization certificates. These logical certificates are not PSC
refutations. A 1,000-candidate prefix establishes no consistency statement.

The same source also repairs a local inference in Friedman's *Simplified
axioms for class theory*, Theorem 3.21, printed page 19. Untagged union coverage
does not ensure every input is covered through its own pair encoding. Its
finite counterexample and disjoint-tag repair were checked against the primary
PDF. Distinct input/output tags make extraction valid, and a triple Union
bounds witnesses; the tagged input set is bounded inside a double power set,
without Replacement or Choice. This repairs that inference under the stated
set-existence assumptions, not the global NBG equivalence. The host preserves
the exact example, source link, assumptions and proof.

Complete reference languages remain eligible minimization targets alongside
the attributed complete 253-state frontend. The new 270-state grammar artifact
is a separate rearrangement of the *original* complete equality calculus;
it is not a compilation of this ground-clause algorithm, and the prior
complete-word public-backend control already reaches 269 states.

