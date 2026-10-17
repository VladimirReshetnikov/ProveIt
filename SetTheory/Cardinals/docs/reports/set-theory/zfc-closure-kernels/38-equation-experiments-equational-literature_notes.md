# Literature and status audit

Prepared 16 October 2026. These notes support the main ProveIt report and the
separate `cyclic_proposal.md`. Repository observations are snapshots, not claims
that every public implementation has been found. No new TM state record is
claimed by these notes.

## 1. What exactly has to be established

For a standard deterministic one-tape, two-symbol, blank-input machine `M`, the
requested theorem is

`ZFC ⊢ (M does not halt ↔ Con(ZFC))`.

One useful route is an internally provable equivalence between finite halting
traces and finite refutations of an effective theory `T`, followed by an
internally provable equivalence `Con(T) ↔ Con(ZFC)`. A theorem merely saying
that nonhalting is unprovable in ZFC supplies less information. A metatheoretic
proof assistant theorem connecting two external inductive predicates is also
not automatically the displayed arithmetized ZFC theorem: the encodings,
translations, and their totality still have to be internalized.

If the exact equivalence is available, ordinary consistency of ZFC rules out a
ZFC proof of nonhalting by the second incompleteness theorem. Ruling out a ZFC
proof of halting needs an additional soundness hypothesis, such as Sigma-1
soundness, unless an independent argument is supplied. Mere consistency does
not in general prevent an effective arithmetic theory from proving its own
inconsistency. This distinction should survive any informal phrase such as
“independent machine.”

“Finite axiomatization” likewise has several meanings. A finite nonlogical
theory can still require a large logic engine. A finite number of schematic
patterns can require expensive instantiation checks. A single formula may
contain a long encoded program. The comparison unit is the complete blank-tape
transition table, including the loader, under one fixed machine convention.

## 2. Public implementation snapshot

The main Jeff repository README is a primary source:

https://github.com/jeff87654/busy-beaver/blob/main/ZF/README.md

The observed README blob hash was
`cf1d5da7fa61a9ad325be9a82d226a9aec20bfbc`. It still advertises the 254-state
verified machine, with theorem names

```
zf254_halts_iff_ZF  : halts tm c0 <-> ZFc ⊢TC ⊥
zf254_halts_iff_ZFC : halts tm c0 <-> (ZFc + AC) ⊢TC ⊥
```

Its exact meanings of `ZFc`, Foundation, and Choice must be read from the
imported Coq library, rather than inferred from the acronym. In the current
README, `ZFc` is the universally closed ZF presentation without Regularity;
the AC statement is an ordinary set-theoretic choice axiom. The separate
335-state line includes Regularity and AC. The README also records the
338/336-family replacement refactoring and the replacement of two
propositional axiom patterns by the BY pattern

`p -> ((-.q -> ((q -> r) -> -.p)) -> q)`.

The more recent primary source is **open PR 20**:

https://github.com/jeff87654/busy-beaver/pull/20

Observed head:
`0d544f2a2e3c18f12278441a74b7879f31cbe856`, branch
`mira-emmy:zf253-exact-equivalence`. Created 2026-10-15 23:50:55 UTC;
last observed update 2026-10-16 00:26 UTC. The pull request was open and not
merged when inspected. Its title is “ZF253: verify a 253-state machine for
finite ZF/ZFC refutations.” The record comparison must therefore include this
253-state candidate rather than stopping at the main README's 254.

The PR describes 253 working states plus terminal label 253, with blank symbol
0 and start state 0. Its reduction reuses a state for two phases: initialization
reads 0, while the runtime helper reads 1; it removes an old initialization
state and renumbers. The body gives an exact 312,975-step blank initialization
to the register-machine handoff and claims closed-assumption Coq endpoint
checks plus recursive `coqchk`. These are the author's CI claims, not a claim
that this literature agent reran the Coq build. The PR explicitly distinguishes
external finite-refutation equivalence from a formalized independence theorem.

Identifiers supplied by the PR:

| Artifact | SHA-256 |
|---|---|
| 253-state machine | `84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95` |
| 254-state baseline | `d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb` |
| Register program input | `1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746` |

The parent report independently audits the ProveIt commits and local checks;
these notes do not duplicate that work. ProveIt already has several proposed
252/250/248/251-state equality-deletion variants whose logical frontends fail
specific countermodels. Their raw state counts cannot be reported as valid
consistency machines.

### The older 7,910-state milestone has a different logical target

Yedidia and Aaronson's original primary paper is

https://arxiv.org/abs/1605.04343

It uses a finite combinatorial search related to Friedman's order-invariant
graphs. It is a historical milestone for a small ZFC-unprovable nonhalting
claim. It is not evidence, by itself, for an exact equivalence to `Con(ZFC)`.
A compressed retelling of the later proof-enumerator lineage should not
retroactively describe the original 7,910-state construction as direct ZFC
refutation enumeration.

## 3. Minimalist alternatives and their actual tradeoffs

| Route | What the primary literature supplies | What remains costly or unproved for this task |
|---|---|---|
| Existing Megill/Tarski-style schema system | A small logical basis with substitution/generalization control, already used by the current record lineage | Equality and variable-instantiation completeness cannot be removed by inspection; successful state savings need a preserved refutation endpoint |
| Condensed detachment | Finite branching in the sense that each pair of prior lines has at most one normalized most-general conclusion | The unifier must handle variable renaming, occurrence checking, substitution propagation, and normalization; fewer choices need not mean fewer binary states |
| Finite GB/CGB class theory | A genuinely finite first-order conservative source theory for ZF; ordinary set AC can be added if desired | Class sorting and finite class-comprehension operations lengthen the source sentence; finiteness does not make the underlying first-order checker disappear |
| Craig–Vaught/Kleene finite extension | General finite axiomatizability after adding predicates under appropriate hypotheses | The construction may encode syntax and satisfaction machinery; it guarantees existence, not a short source or a small loader |
| Df3 plus cyclic compression | A full-first-order validity reduction to one-generator algebra, then the seven explicit equations proved in the companion note | The full source-to-Df3 compiler and literal consistency target have not been implemented; target growth could erase the small kernel advantage |
| SK combinatory logic / binary lambda calculus | Universal computation with extremely small algebraic languages and compact program encodings | The set-theory proof recognizer remains in the closed program; evaluator, target, and blank loader must all be counted, and conversion/halting correctness must be proved |
| Single “set theory” axiom | Some published single axioms capture particular weaker set theories | The word “set theory” does not imply ZFC consistency strength; a correct two-way interpretation is indispensable |

The last two rows are useful controls on the novelty claim. A seven-equation
basis is not the smallest conceivable equational computational substrate: the
standard two SK equations already support universal computation. The point of
the Df3 route is that a published logical translation may move foundational
content into one relatively structured algebraic query. Whether that beats a
compiled SK proof-search program or the current specialized code is empirical.

### Megill: useful, but the sense of finiteness matters

Norman Megill, *A Finitely Axiomatized Formalization of Predicate Calculus with
Equality*, Notre Dame Journal of Formal Logic 36 (1995), 435–453.

Author preprint with errata:
https://us.metamath.org/downloads/finiteaxiom.pdf

The paper's system S1 has fourteen logical axioms and condensed detachment and
generalization. Primitive free-variable/proper-substitution checks are absent;
completeness is established through the relation to S2. The term “finitely
axiomatized” means that each individual proof step has finitely many choices.
The first-page note records two missing lemmas in the original Substitution
Theorem proof, with repairs discussed in 2017 but not yet integrated into the
preprint. That is a source-version caveat, not evidence that the repaired
system is unsound. A modern formal endpoint should import the actual repaired
proof, rather than rely on the title or omit the unification side conditions.

### Finite class theory: a concrete source for the algebraic proposal

Hajnal Andréka and István Németi, *Végesen axiomatizált
cilindrikus-Gödel–Bernays-halmazelmélet* [Finitely axiomatized cylindric
Gödel–Bernays set theory], in *Nehogy érvgyűlölők legyünk*, 2013, pp. 184–192.

Author manuscript:
https://old.renyi.hu/pub/algebraic-logic/ANCGB13.pdf

Theorem 1, printed page 189, states syntactic conservativity over ZF after
relativizing set variables to the class `V` of sets. The proof describes
algorithms transporting proofs. Its finite axiom families include
extensionality, class Boolean operations, three cylinder closures, diagonal
and membership classes, class products, class-functional images of sets,
Infinity, Pairing, Power Set, Union, and Foundation. This provides the finite
`σ` selected in the companion proposal. It does not use Choice.

For ordinary consistency strength, adding Choice is harmless by Gödel's
constructible-universe argument. The selected source is therefore CGB without
AC, with the explicit chain `Con(CGB) ↔ Con(ZF) ↔ Con(ZFC)`. This choice avoids
confusing global class Choice with ordinary set Choice. The reference to a
finite source does not mean that this artifact has printed its fully expanded
conjunction or the Df3 translation of its negation.

### The decisive weak-logic reference is the 2013 published theorem

Hajnal Andréka and István Németi, *Reducing First-order Logic to Df3, Free
Algebras*, in *Cylindric-like Algebras and Algebraic Logic*, Bolyai Society
Mathematical Studies 22 (2013), 15–35.

DOI: https://doi.org/10.1007/978-3-642-35025-2_2

Author manuscript: https://old.renyi.hu/pub/algebraic-logic/CAIII-ANpaper.pdf

Theorem 1.6(i) supplies a computable translation from full relational
first-order logic, with equality, into the three-variable one-atom system,
preserving and reflecting consequence. Remark 1.3(ii) identifies its proof
Lindenbaum algebra with the one-generated free Df3 algebra. Taking empty
premises produces the validity-to-identity reduction needed by the proposal.
Remark 1.8(iv) warns that the translation need not preserve negation. The
published proof cites the earlier 2011 manuscript and supplementary notes.

Earlier source: *Formalizing set theory in weak logics, searching for the
weakest logic with Gödel's incompleteness property* (2011),
https://arxiv.org/abs/1111.0995 . Its explicit finite Df3 equational basis is
useful, but its presentation qualifies the scope of the included proof of the
general validity translation. This is why the 2013 theorem is the proposal's
declared bridge. The supplementary Part II URL referenced there,
https://www.math-inst.hu/pub/algebraic-logic/LapomDf2011b.pdf , was not accessible
through the research tool, including the `renyi.hu` and `old.renyi.hu` aliases.
No claim of a separately audited executable implementation is made.

### Boolean single-axiom compression is proved; set-theory strength is separate

William McCune, Robert Veroff, Branden Fitelson, Kenneth Harris, Andrew Feist,
and Larry Wos, *Short Single Axioms for Boolean Algebra*, Journal of Automated
Reasoning 29 (2002), 1–16.

DOI: https://doi.org/10.1023/A:1020542009983

Author manuscript: https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf

The paper proves the 15-symbol NAND axiom used verbatim as Sh1 in the companion
kernel, and establishes minimality under its single-axiom length convention.
No claim is made that 15 symbols minimize an interpreter or an extended
algebraic theory. Their machine-search proof artifacts are linked from
https://www.cs.unm.edu/~mccune/papers/basax/ .

By contrast, David Bennett's *A Single Axiom for Set Theory*, Notre Dame Journal
of Formal Logic 41(2) (2000), 152–170,
DOI https://doi.org/10.1305/ndjfl/1038234609 , explicitly describes its theory as
stronger than Zermelo set theory but weaker than ZF in its abstract. The
[primary PDF](https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-41/issue-2/A-Single-Axiom-for-Set-Theory/10.1305/ndjfl/1038234609.pdf)
therefore does not furnish the required ZFC equivalence merely by being a
single set-theoretic axiom. This route was not adopted.

### General finite extension and generic computational encodings

William Craig and Robert L. Vaught, *Finite Axiomatizability using additional
predicates*, Journal of Symbolic Logic 23(3) (1958), 289–308,
DOI https://doi.org/10.2307/2964289 .

The publisher's extract distinguishes syntactic and semantic finite extensions
and records Kleene's finite-axiomatizability result for recursively
axiomatizable finite-signature theories without equality, and for theories
with equality having only infinite models. These results explain why a finite
source is possible, but do not provide a concrete small-state advantage.

John Tromp, *Binary Lambda Calculus and Combinatory Logic*, Dagstuhl Seminar
Proceedings 06051 (2006), 1–20,
DOI https://doi.org/10.4230/DagSemProc.06051.4 .

The paper develops explicit binary encodings and parser-interpreters. Its
current author file at https://tromp.github.io/cl/LC.pdf is a revised manuscript
dated 24 September 2026, titled *Functional Bits: Lambda Calculus based
Algorithmic Information Theory*. The revised text still illustrates
substantial expansion under naive bracket abstraction, and improvements from
careful compilation. These program lengths are **bits in the author's
functional language**, not binary TM working-state counts. Exact historical
bit numbers should be pinned to one version if reported.

## 4. Primary references for Choice and mechanization scope

Kurt Gödel, *The Consistency of the Axiom of Choice and of the Generalized
Continuum-Hypothesis*, PNAS 24(12) (1938), 556–557,
DOI https://doi.org/10.1073/pnas.24.12.556 .

https://pmc.ncbi.nlm.nih.gov/articles/PMC1077160/pdf/pnas01800-0034.pdf

Kurt Gödel, *Consistency-Proof for the Generalized Continuum-Hypothesis*, PNAS
25(4) (1939), 220–224,
DOI https://doi.org/10.1073/pnas.25.4.220 .

https://pmc.ncbi.nlm.nih.gov/articles/PMC1077751/

The latter explicitly treats Zermelo's axioms with or without the substitution
axiom and sketches the constructible-universe method. It is a suitable primary
historical reference for the mathematical relative-consistency bridge.

Lawrence C. Paulson, *The Relative Consistency of the Axiom of Choice Mechanized
Using Isabelle/ZF*, LMS Journal of Computation and Mathematics 6 (2003),
198–248, DOI https://doi.org/10.1112/S1461157000000449 .

Technical-report version:
https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-551.pdf

Current session documentation:
https://isabelle.in.tum.de/library/FOL/ZF-Constructible/document.pdf

Paulson's abstract explicitly flags the burden of metatheory and two parts of
the original formalization that do not fit together without further
internalization. It is strong evidence of the mathematical construction and
valuable formal infrastructure, but should not be cited as if it alone were
the fully internalized end-to-end theorem requested for an arbitrary TM.

## 5. Practical priorities arising from the research

1. Treat the exact 253-state public table as the current comparison point and
   finish the precise external-to-internal and theory-strength bridges for it.
2. Retain the complete logical engine when benchmarking new encodings. A
   smaller refutation fragment needs a proof of refutation completeness, not
   just successful examples or sampled nonhalting runs.
3. For a new algebraic route, generate the actual finite source sentence,
   translate its **negation**, emit the actual one-generator target, and record
   the target size before estimating any TM state saving.
4. Benchmark the seven-equation cyclic kernel against direct Df3 and a generic
   SK or small rewriting frontend. The count of axioms alone decides none of
   these comparisons.
5. Require a complete blank loader, total per-candidate checker, fair exhaustive
   search, complete machine table, and formal simulation for any claimed state
   record. Finite boot checks and negative certificate tests are useful
   evidence for specific components, but cannot prove infinite nonhalting.

The companion kernel makes one part of this program concrete: its exact seven
equations, complete ground rewrite witness format, and executable negative
tests are available now. Its remaining set-theoretic payload and TM compiler
are stated as open work instead of being hidden behind the word “finite.”
