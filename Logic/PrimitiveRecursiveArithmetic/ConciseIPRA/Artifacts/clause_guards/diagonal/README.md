# A clause presentation with substitution-stable introduction

This directory supplies a complete readable proof checker for a five-pattern
raw presentation of iPRA, a matching native six-pattern control, an exact
upstream witness-mode clause control, proof producers, implementation checks,
and exact translations of primary certificates into the native control.

The proposed interface combines existing ingredients: the two-case evaluation
rule, reusable clause contexts, and the diagonal introduction guard. It deletes
Q from the formula grammar and combines hypothesis use and Q elimination into
clause use. Its introduction mode depends only on the protected bound-variable
shape of the matrix. Consequently simultaneous substitution for free parameters
preserves every rule instance, including its mode. There is no term normalization,
equality template or witness-zero test.

This is a simplification of the substitution-stable native interface. It does
not dominate every smaller checker in the repository, and its component
mathematics is inherited. The report states the exact theory equivalence and
both interpretation round trips. The Python code and tests are not a new
Lean or Rocq formalization.

## Main files

- `checker.py`: complete trusted primary checker.
- `native_diagonal_control.py`: matching complete native Eq/Q/D control.
- `witness_control.py`: exact upstream raw two-case clause checker with the
  witness-zero introduction convention.
- `FORMAT.md`: syntax, scopes, primitive instructions, input and output.
- `proof_tools.py`: untrusted arithmetic proof producers, direct parameter
  substitution and primary-to-native certificate translation.
- `verify.py`: finite checks, certificate generation and complete-module metrics.
- `results.json`: output from the reproduction run.
- `examples/`: accepted primary/native certificates and rejected controls.
- `source_provenance.json`: source pin, attribution and source identity.
- `witness_to_diagonal.diff`: the exact source delta from the witness control.
- `native_to_clausal.diff`: the exact source delta deleting native Q syntax.

Neither trusted checker imports any producer, test helper, source-control
client, external theorem database or nonstandard Python package.

## Run

```sh
python3 verify.py
python3 checker.py < examples/diagonal_progress_uses_hypothesis.json
```

Successful checking requires exit status zero and exactly the output `ACCEPT`.
The acceptance path contains no `assert` statement; Python `-O` has the same
intended proof-checking behavior. The public checker accepts closed Eq/D goals.
The internal derivation relation also supports open formulas and clause contexts;
the public command-line format does not allow a caller to inject hypotheses.

## Controlled measurements

Reference runtime: CPython 3.12.14. Remove actual module/function/class docstrings,
normalize the entire module using `ast.unparse`, and append one LF. Comments are
removed by parsing. Names of common functions and variables are identical in the
matched source family. Descriptive titles are not counted in normalized sizes.

| Complete module | Patterns | Normalized bytes | Tokens | AST nodes |
|---|---:|---:|---:|---:|
| Native diagonal control | 6 | 3395 | 975 | 1138 |
| Proposed diagonal clause checker | 5 | 3056 | 872 | 1013 |
| Existing witness-mode clause checker | 5 | 2956 | 837 | 977 |

The matched native reduction is 339 bytes, 103 tokens and 125 AST nodes. Against
the existing witness-mode clause checker, the proposal adds 100 bytes, 35 tokens
and 36 AST nodes. The latter is the concrete cost of the new substitution-stable
mode convention in this implementation. No new global byte minimum is claimed.
Raw source sizes and both raw/normalized deterministic gzip-9 sizes are recorded
separately in `results.json`; they are not presented as arithmetic simplifications.

The historical 516-byte arity envelope omits its public-goal grammar validator.
The separate 860-byte validated Eq/Q/D codec has a different certificate protocol
and retained administrative formula representation. Neither is surpassed here.

## What was checked

The reproduction run checks 12 accepted primary proofs, 17 malformed or invalid
certificates, 12 exact end-formula translations to the native diagonal control,
5 free-parameter substitutions with eigenparameter renaming, 600 generated
well-formed matrices for guard preservation/reflection, 4 independently stated
capture controls, and 82 command-line runs in ordinary and optimized Python.

The selected diagonal proof really uses its progressive branch hypothesis;
changing that hypothesis to the zero base invalidates the same proof tree.
Its end equation is reflexive, so the example checks mode behavior and proof
substitution, rather than claiming an independent deep arithmetic theorem.
Other examples exercise both evaluation cases, derived equality, nested
iterator templates, canonical clause use with its necessary base, nested D,
repeated clause use, and strict scope/type rejection.

These finite checks are implementation evidence. They do not prove soundness,
completeness, or bi-interpretability for all derivations. Those are the written
metatheorems, composed with the pinned repository's native/iPRA bridge.

## Provenance

Pinned repository commit:
`443cff49563457a48ee0f663012d56c4bdb58fa0`.

The exact source of `witness_control.py` is:
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/rootfree_clausal/code/raw_two_case.py`.
The proposed primary changes only its explanatory module docstring, adds the
matrix guard, and replaces the introduction's mode expression. The native
control changes only the formula/context representation and the hypothesis/QE
interface necessary to reproduce the six-pattern native calculus; the term,
evaluation and introduction components retain the same implementation.

The clause presentation, two-case evaluation, diagonal guard and whole-domain
native/iPRA equivalence are credited to ProveIt contributors. Reused source is
licensed under the upstream MIT No Attribution license in `LICENSE-upstream.txt`.
