# Formal languages in intuitionistic primitive recursive arithmetic

Research package prepared for Vladimir Reshetnikov, 22 November 2026.

Start with **formal_languages_ipra.pdf**. The editable master source is
`formal_languages_ipra.tex`, with all included chapter files under `chapters/`.

## What is delivered

The report contains **100 numbered mathematical results**, including supporting
lemmas, with full human-readable arguments, primitive-recursive algorithms,
explicit witness bounds, and quantifier-free induction invariants. Definitions
are not included in the count. `evidence/theorem_catalogue.json` records each
result's label, title, report number, and source chapter.

The main developments are:

- Word coding, cancellation, Levi factorization, commuting words, free-monoid
  laws, effective language algebra, star, homomorphisms, and Arden's lemma.
- DFA/NFA/epsilon-NFA, regular expressions, and regular grammar equivalence;
  closure, pumping, finite decisions, shortest separators, and minimization.
- Finite-monoid recognition, generated transition monoids, and effective
  syntactic congruence with bounded distinguishing contexts.
- CFG derivation/parse-tree equivalence, nullable/productive computation, CNF,
  CYK, direct chart saturation, finite parse counting, EBNF compilation,
  standard closure, PDA equivalence, pumping, finiteness, and nonclosure.
- Explicit separating words against every DFA or CFG in the indicated
  examples, and a PR diagonal language beyond all noncontracting grammars.
- Noncontracting grammar membership, recognizable language presentations,
  totality-sensitive decisions, halting and complement diagonals, and a PR
  language whose erasing homomorphic image is undecidable.
- Integer recurrence for the word counts of every regular language, rational
  generating series interpreted by finite truncations, unary periodicity,
  balanced-parenthesis parsing, and the exact Catalan formula.

The report's closure table marks cells that are proved, refuted, or not covered.
It does not claim that every statement in the Wikipedia link neighborhood has
been established.

## Exact formal verification status

**The Lean material is uncompiled.** There was no Lean executable in this
workspace, and no Lean build was run. The files are a detailed implementation
blueprint, not completed kernel-checked proofs of the report.

`lean/SemanticCore.lean` is a small candidate semantic core with ordinary proof
scripts and no placeholders. Its lack of placeholders is not a build result.
The `.lean.txt` files deliberately expose specification records and remaining
obligations without presenting them as proved theorems. They provide finite
structures, coding choices, algorithms, witness bounds, and the target
object-theory statements.

The final formalization target is `LeanProofs.ConciseIPRA.Prf PRAAx [] phi` for
each explicit first-order sentence `phi`. A semantic Lean theorem about
natural numbers, lists, or automata alone is not such an object-theory result.
The report and `lean/ObjectTheoryOutline.lean.txt` give the completion order
and build/audit gates.

The source interfaces were inspected at ProveIt commit:

`3eb195cab4cc3d552a9eca78880c6d428f3e44f9`

The repository toolchain at that revision is `leanprover/lean4:v4.32.0`.
ProveIt itself was not built or changed in this session. The immutable source
paths inspected are in `evidence/repository_snapshot.json`.

## Constructive conventions

1. Finite descriptions are numerical input; languages are presented predicates,
   not arbitrary elements of a power set.
2. Every PR predicate is a fixed definition. There is no assumed universal
   primitive-recursive evaluator for all PR programs.
3. Bounded machine simulation is total; unbounded search is a certificate
   existential and is not silently assigned a termination proof.
4. RE star and substitution carry explicit lists of certificates. Unbounded
   finite collection is not inferred from separate existence assertions.
5. The two-recognizer theorem includes an exhaustiveness premise internally;
   complement nonrecognizability is proved directly by diagonal contradiction.
6. Myhill-Nerode uses supplied effective finite-congruence data. Quotients by
   arbitrary unknown languages are not silently turned into DFA algorithms.

## Files

| Path | Purpose |
|---|---|
| `formal_languages_ipra.pdf` | Complete report |
| `formal_languages_ipra.tex`, `chapters/` | Complete LaTeX source |
| `lean/` | Candidate semantic core and detailed formalization blueprints |
| `verification/regular_reference.py` | Automata reference algorithms and independent finite checks |
| `code/grammar_reference.py` | Arbitrary-CFG chart parser, normalization, CYK, parse certificate checker |
| `code/word_count_reference.py` | Word/cut algorithms, commuting-word witnesses, Catalan reflection, matrix recurrence |
| `qa/`, `verification/regular_check_results.json` | Executed check results and PDF validation ledger |
| `evidence/` | Repository/source provenance, proof reviews, theorem catalogue |
| `tools/build_pdf.py` | Local TeX builder, including recovery from absent format/font caches |
| `tools/make_catalogue.py` | Theorem inventory and source cross-reference checks |
| `SHA256SUMS` | Checksums for the included deliverables |

## Reproduce the executable checks

Only Python's standard library is needed:

```bash
python3 verification/regular_reference.py
python3 code/grammar_reference.py
python3 code/word_count_reference.py
python3 tools/make_catalogue.py
```

The finite checks passed. They compare different implementations and check
reconstructed certificates; they are not formal proofs or exhaustive tests of
the unbounded theorems. See the report and JSON receipts for exact scope.

## Rebuild the PDF

With a normal TeX Live installation:

```bash
python3 tools/build_pdf.py formal_languages_ipra.tex --out-dir build --system
```

In an environment with the TeX sources installed but missing generated formats
or file databases, omit `--system`; the helper prepares a local runtime using
the installed sources and fonts. No downloads or system modifications are
needed for that mode in the environment where this report was produced.

The required packages are ordinary TeX Live packages: Latin Modern, AMS,
geometry, microtype, booktabs, longtable, enumitem, fancyhdr, listings, xurl,
and hyperref.

## Lean starting point

After installing the pinned Lean toolchain, the small standalone semantic
candidate can be checked with:

```bash
cd lean
lake env lean SemanticCore.lean
```

The subject outlines are intentionally `.lean.txt`: their outstanding proof
obligations must be implemented, not enabled as new axioms. Object-theory
modules belong in a checkout of the pinned ProveIt revision with its existing
Lake configuration and dependency lockfile. The archive does not include a
large copy of ProveIt or Mathlib; it records their exact integration points.

## Limits

Not proved here: general CFG equivalence/ambiguity/universality undecidability,
PCP, Parikh's theorem, context-sensitive complement closure, deterministic
context-free and indexed-language closure classifications, full unrestricted
grammar/TM equivalence, infinite-word automata, or power-set cardinality claims
inside iPRA. The report contains no assertion of a completed Lean formalization.
