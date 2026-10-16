# A binary certificate format for pure equality-free PSC

This directory supplies a **reference derivation checker**, an actual harmless
example certificate, and reproducible regression tests. It does **not** supply a
new Turing-machine transition table, a state-count improvement, a Lean/Coq proof,
a proof of the consistency of set theory, or a formal proof translation to ZFC.
Its purpose is to make the proposed proof-search target completely explicit and
reviewable before compiler work.

The checker accepts a refutation exactly when a certificate is a valid derivation
in the calculus below and its last line is the literal primitive `Bottom`.
`Mem(0,0)` is a different formula and is never used as a falsity abbreviation.

## Files and reproduction

- `psc_checker.py`: self-contained Python 3 reference checker and encoder.
- `test_psc_checker.py`: syntax, capture avoidance, rule, and resource regressions.
- `validate.py`: produces `validation.json`, including all bitstrings of length
  at most 16 and an optional comparison with the pinned ProveIt schema generator.
- `identity.cert`: exactly 80 ASCII `0`/`1` characters, without a trailing newline;
  a valid five-line proof of `Mem(0,1) -> Mem(0,1)`, **not** a refutation.
- `validation.json`: recorded results and hashes of the code actually tested.
- `provenance.json`: upstream pin, URLs, and hashes of source files consulted.

From this directory, using Python 3.10 or newer and no third-party packages:

```sh
python -m unittest -v test_psc_checker
python psc_checker.py check identity.cert
python validate.py
```

For an optional exact-byte comparison of generated formulas with a separately
obtained pinned source file:

```sh
python validate.py --upstream-kernel /path/to/kernel_metrics.py
```

The command `check` reports two different facts, `valid_derivation` and
`accepted_refutation`. Its successful exit code denotes a well-formed derivation;
the JSON flag identifies whether that derivation ends in Bottom. The included
identity certificate has `valid_derivation: true` and
`accepted_refutation: false`.

## Language, variables, and abbreviations

Use classical first-order logic over nonempty structures, with one binary
relation symbol, no function/constant symbols, and no equality symbol. Variable
names are natural numbers. Formula constructors are

\[
  \bot,\qquad x\in y,\qquad A\to B,\qquad \forall x\,A.
\]

`Bottom` denotes false. Derived connectives have the following **exact syntax**;
the generator does not normalize double negations:

\[
\begin{aligned}
\neg A&=(A\to\bot),\\
\exists x A&=\neg\forall x\neg A,\\
A\land B&=\neg(A\to\neg B),\\
A\lor B&=(\neg A\to B),\\
x\subseteq y&=\forall z(z\in x\to z\in y),
\end{aligned}
\]

where the last displayed bound variable is fresh for its two arguments.
Exact formula comparison compares named syntax. It does not silently identify
alpha-equivalent formulas or apply a propositional simplifier.

## The only nonlogical axiom schema

Take **any** formula `rho` in this language. Free variables 0 and 1 denote input
and output; other free variables are parameters. The designated variables may
be absent, and they may also have bound occurrences inside the matrix. Bound
occurrences are never renamed by substitution for a free variable. There is no
positivity restriction on the matrix.

Write `rho(x,y)` for simultaneous capture-avoiding replacement of its free
variables 0 and 1. Let

\[
\mathrm{SB}_{\rho}:=
 \forall x\exists b\forall y(\rho(x,y)\to y\subseteq b).
\]

The generated axiom is the universal closure over all remaining free parameters
of

\[
\mathrm{SB}_{\rho}\to\forall a\exists C\left[
 \forall x\forall y\bigl(
  (((x\subseteq a\lor x\in C)\land\rho(x,y))\to y\in C)\bigr)
 \land
 \forall y\bigl(y\in C\to\exists x\rho(x,y)\bigr)
\right].
\]

In particular, support uses an unrestricted global witness `x`. It does not
require that witness to belong to the hull or its seed. The instance has no
extensionality axiom, profile-congruence axiom, or built-in Foundation axiom.

For deterministic named syntax, the generator takes `m` to be one greater than
the largest name anywhere in the matrix, including bound occurrences and the
names 0 and 1. It assigns `x,y,b,a,C,z` the names `m,...,m+5`, in that order.
It then adds outer universal parameter quantifiers in increasing order of their
names, smallest outermost. This matches the unnormalized `seeded` schema with
`seed='subset', mixed=False` in the pinned ProveIt `kernel_metrics.py`, after
expanding negation into implication to Bottom. Tests compare six matrices,
including parameters, shadowed distinguished variables, and negative matrices.

## Binary grammar

Every natural `n` is represented by `0^n1`. For example, 0 is `1`, 1 is `01`,
and 2 is `001`. A formula is a prefix expression:

| Prefix | Following fields | Formula |
|---|---|---|
| `00` | none | Bottom |
| `01` | natural `x`, natural `y` | `Mem(x,y)` |
| `10` | formula `A`, formula `B` | `Imp(A,B)` |
| `11` | natural `x`, formula `A` | `All(x,A)` |

A certificate starts with its unary line count `N`, then exactly `N` encoded
lines. Each line starts with a three-bit opcode and its fields below. Line
numbers start at zero. There is **no** separate claimed-conclusion field: the
checker reconstructs the conclusion of each line. No bits may remain after the
last line. The one-bit string `1` is the empty derivation, with no conclusion;
it is not a refutation. A text file must contain only ASCII `0` and `1`, without
whitespace or a trailing newline.

| Opcode | Fields, in order | Formula produced / condition |
|---|---|---|
| `000` K | formulas `A,B` | `A -> (B -> A)` |
| `001` S | formulas `A,B,C` | `(A -> (B -> C)) -> ((A -> B) -> (A -> C))` |
| `010` C | formulas `A,B` | `((A -> Bottom) -> (B -> Bottom)) -> (B -> A)` |
| `011` UI | naturals `x,y`; formula `A` | `All(x,A) -> A[x:=y]`, capture avoiding |
| `100` UD | natural `x`; formulas `A,B` | `All(x,Imp(A,B)) -> Imp(A,All(x,B))`; require `x` not free in `A` |
| `101` PSC | formula `rho` | closed schema instance specified above |
| `110` MP | natural indices `i,j` | require `i,j` strictly earlier, and line `j` exactly `Imp(line i,B)`; produce `B` |
| `111` GEN | natural index `i`, natural `x` | require `i` strictly earlier; produce `All(x,line i)` |

K, S and the full classical contraposition axiom C give a standard classical
propositional Hilbert basis with primitive falsity. UI, UD and unrestricted
generalization extend this to the usual complete first-order calculus for the
equality-free relational language. There are no undischarged assumptions. PSC
axioms are closed; logical axiom instances and intermediate theorems may be open.
The rule fields carry arbitrary formulas and variable names, so every finite
derivation in this calculus has a finite certificate in this format.

## Capture avoidance

Substitution is simultaneous. At a quantifier, a substitution for that bound
name is removed. Only substitutions whose source names are free in the body
remain active. If the binder occurs among their target names, it is renamed to
a fresh natural, larger than every name in the entire original formula and in
the initial substitution; subsequent renamings increase that fresh counter.
Its bound occurrences are renamed through a child substitution environment,
which is itself shadowed correctly by any nested binder of the original name.

For example, substituting `0 := 1` into `All(1,Mem(0,1))` produces
`All(2,Mem(1,2))`. It does not produce `All(1,Mem(1,1))`.

## Why the checker recognizes exactly the specified finite derivations

Parsing has one unambiguous prefix case for each formula constructor, a
terminating unary delimiter for each natural, and one fixed field signature per
opcode. Every successful parse consumes exactly the declared certificate. Each
formula is represented by an interned node ID; an implication comparison for MP
is consequently an exact syntax comparison, without recursive Python equality.

Induct on line number. K, S, C, UI and UD lines are exactly their displayed
logical axiom instances, with the UD side condition checked and UI substitution
performed capture avoiding. A PSC line is exactly its closed generated axiom.
MP and GEN use only earlier formulas, and they implement the displayed inference
rules. Hence every returned line is derivable in the specified theory. Conversely,
encode any finite derivation line by line, including its chosen axiom parameters
and earlier-line references. Induction shows that the checker reconstructs the
same lines. Named-syntax choices for alpha conversion are explicit and ordinary
alpha-renaming consequences can be proved in the calculus when needed.

For semantic soundness, K/S/C are classical tautologies; UI is universal
instantiation with capture avoidance; UD is valid because its antecedent `A`
does not depend freely on the quantified variable; MP preserves validity; and
GEN preserves validity for theorems from closed nonlogical axioms. PSC lines are
assumptions of the target theory. This reasoning establishes relative soundness
of the calculus, not the existence of a model of PSC.

Enumerating all finite bitstrings in length-then-lexicographic order and halting
exactly when `accepts_refutation` returns true halts iff this calculus derives
Bottom. Every finite candidate is processed in finite time in the mathematical
algorithm, and every finite derivation eventually occurs. That elementary
syntactic equivalence requires no assumption that PSC is consistent. Relating
`Con(PSC)` to `Con(ZFC)` requires the separate mathematical proof translations
discussed in the report; those translations are not implemented in this checker.

## Verification boundary and engineering implications

The formula arena, parser, encoder, and substitution traversal use explicit
stacks and integer node IDs, with no recursion-depth or proof-length cap imposed
by the checker. A test exercises 5,000 nested quantifiers. This avoids a common
accidental restriction to bounded-depth proofs. It does not make physical Python
execution infinite: memory, host execution time, integer/object limits, and the
operating system remain finite. `MemoryError` and other resource failures
propagate and must never be read as certificate rejection or consistency evidence.
The only errors turned into `false` by `accepts_refutation` are ordinary finite
syntax or inference errors. The abstract unbounded-memory implementation is the
one intended for a future Turing-machine compilation.

The validation record includes 12 unit tests, 12,000 finite-model comparisons of
capture-avoiding substitution, the real identity proof, and all 131,071 bitstrings
of length at most 16. The latter include 938 valid derivations and no refutations.
This very short exhaustive census is a parser/kernel regression only. It offers
no evidence of consistency, practical proof-search performance, or machine size.

Binary proof checking itself is an existing approach. The repository already
contains executable Hilbert certificates in its BIC research artifacts:
`01-bic-logic.py`, `01-bic-bic.py`, and
`01-bic-notes-CERTIFICATE_FORMAT.md`, under
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/` at commit
`b07d1a27bbe2814f2fd84cc55feef71c4de5b2db` and retained at the reviewed snapshot.
The new work here extends that direction with pure PSC, the exact binary selector
format above, and this reference kernel; no priority for proof checking in
general is claimed. The format
is intentionally conservative: eight selectors fit exactly three bits, but that
does not establish a small compiled machine. Formula interning, variable-set
bookkeeping, unary labels, and stored prior lines all have implementation costs.
Compiler lowering, a fair unbounded enumerator, blank-tape initialization, a
literal binary transition table, and a theorem identifying that table with this
proof predicate remain separate work.
