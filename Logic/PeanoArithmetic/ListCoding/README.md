# Coding finite lists in Peano arithmetic

This project gives independent Lean 4 and Rocq/Coq proofs that finite lists of
natural numbers can be coded by single natural numbers and that twenty-five
standard list and number-theoretic predicates are definable by genuine
first-order formulae in the language of Peano arithmetic.  It also develops a
shared natural-number coding of hereditary Cantor normal forms below `ε₀`.
Each port exports five further PA formulae for validity, strict order,
addition, multiplication, and exponentiation, bringing its audited formula
total to thirty.  Rocq also independently verifies the raw coding and its
syntactic normal-form, order, and arithmetic properties.

The formulae have only the symbols of arithmetic—zero, successor, addition,
multiplication, and equality—together with first-order logical connectives and
quantifiers. Their displayed numeric arguments are free variables, or
**parameters**, of those formulae. No list type, semantic oracle, or additional
list-valued function symbol is added to PA's object language.

## List codes

Both developments use a canonical functional sequence representation with the
same public contract:

- every external finite list of natural numbers has a single-natural-number
  code;
- every valid code decodes to exactly one finite list;
- encoding followed by decoding returns the original list;
- equality of canonical encodings implies equality of lists; and
- malformed natural numbers are separately recognized as invalid; if an
  implementation uses a totalized decoder with a default result, that result
  confers no list meaning without the validity guard.

The concrete encodings are deliberately allowed to differ. Lean specializes
the sequence coding already provided by
`FormalizedFormalLogic/Foundation`: a list is the Ackermann code of the graph
of a function whose domain is an initial segment. Coq uses a self-delimiting
nested polynomial code, with zero for the empty list and a positive paired
node for a head and the strictly smaller code of its tail. The round-trip and
functionality theorems, rather than accidental equality of the two numeric
encodings, are the parity boundary between the ports.

List positions are **zero based** throughout. Thus element zero is the first
element, and asking for an element at an index greater than or equal to the
length is false. This is separate from the explicitly one-based enumeration
of primes introduced below.

## Represented predicates

For the following descriptions, `decode(v) = xs` includes the assertion that
`v` is valid. The result code is written first in constructor-like relations.

1. **Valid code**: `p` decodes to some finite list.
2. **Length**: `v` decodes to `xs` and `length xs = n`.
3. **Element**: `v` decodes to `xs` and the zero-based `k`-th element of `xs`
   is `m`.
4. **Singleton**: `v` decodes to exactly `[m]`.
5. **Concatenation**: `v`, `t`, and `u` decode to `xs`, `ys`, and `zs`, and
   `xs = ys ++ zs`.
6. **Flattening**: `w` decodes to a list of valid list codes; decoding those
   inner codes in order and concatenating their lists gives the list decoded
   by `v`.
7. **Occurrences**: the list decoded by `v` contains exactly `n` occurrences
   of `m`, including multiplicity and regardless of the other elements.
8. **Permutation**: the lists decoded by `v` and `w` are permutations in the
   usual multiplicity-preserving sense.
9. **Contiguous substring**: the list decoded by `w` is `prefix ++ xs ++ suffix`,
   where `xs` is the list decoded by `v`.
10. **Subsequence**: the list decoded by `v` is obtained from the list decoded
    by `w` by deleting zero or more elements without changing the order of the
    retained elements. Adjacency is not required.
11. **No duplicates**: the list decoded by `v` has pairwise distinct elements.
12. **Nondecreasing order**: each element of the list decoded by `v` is at most
    its successor. Valid empty and singleton lists are sorted.
13. **Lexicographic order**: `v` decodes to a list of valid inner list codes,
    and their decoded lists are in nondecreasing lexicographic order. A proper
    prefix comes first, and otherwise the first unequal elements determine the
    order. Numeric code values themselves are never used as the lexicographic
    keys.
14. **All permutations**: `v` decodes to the canonical lexicographically
    sorted list of codes of all distinct permutations of the list decoded by
    `w`.
15. **Sum**: `p` is the left-to-right sum of the entries decoded from `v`;
    the empty list has sum zero.
16. **Product**: `p` is the left-to-right product of the entries decoded from
    `v`; the empty list has product one.
17. **Greatest element**: `m` occurs in the list decoded from `v` and every
    entry is at most `m`.  This is false for the empty list.
18. **Least element**: `m` occurs in the list decoded from `v` and every entry
    is at least `m`.  This is false for the empty list.
19. **Twice the median**: after sorting the nonempty decoded list, `m` is twice
    its central entry at odd length, or the sum of its two central entries at
    even length.
20. **Unique mode**: `m` occurs in the decoded list and its multiplicity is
    strictly greater than the multiplicity of every different entry.
21. **Nth prime**: `p` is the `n`-th prime, with **one-based** indexing.  Thus
    the first prime is `2`, while index zero has no corresponding prime.
22. **Natural power**: `m = a^k`, including the convention `a^0 = 1` and hence
    `0^0 = 1`.
23. **Prime factorization**: `v` decodes to the strictly prime-sorted list of
    two-entry codes `[p, e]` for the positive prime powers in the factorization
    of `m`.  The factorization of one is empty; zero has no factorization.
24. **Base digits**: `v` is the canonical most-significant-digit-first
    expansion of `m` in base `b`.  Bases are at least two, zero is `[0]`, and
    every other expansion has a nonzero leading digit.
25. **Positive divisors**: `v` is the strictly increasing list containing
    every positive divisor of `m` exactly once.  This is false for zero.

The six scalar relations use the result-first parameter order shown above:
`(p, v)` for sum and product and `(m, v)` for the four statistics.  A scalar
result is an arbitrary natural number, not another list code; only `v` is
subject to the validity guard.

The number-theoretic relations likewise put the constructed result first:
`(p, n)` for the one-based `n`-th prime, `(m, a, k)` for powers, `(v, m)` for
factorizations and divisor lists, and `(v, m, b)` for base-`b` digits.

Every predicate is strict about malformed inputs. If any argument that is
supposed to code a list is invalid, the predicate is false. Flattening and the
two predicates about lists of list codes additionally require every inner code
to be valid. In particular, two invalid numbers are not permutations, an
invalid number is not vacuously sorted, and an invalid inner code cannot be
hidden in a flattening witness.

## Aggregate and statistical conventions

Sum and product are certified by sequences of partial results.  Their initial
values, zero and one respectively, make the empty-list conventions part of
the arithmetic definitions rather than exceptional metalevel cases.

The median relation uses a nondecreasing permutation of the input.  At length
`2k+1` its result is twice entry `k`; at length `2k+2` its result is the sum of
entries `k` and `k+1`.  This is exactly twice the conventional median while
remaining a natural number and avoiding division in the PA formula.  Sorted
permutations have the same order statistics, so the witness cannot change the
result.

For the mode, only values that occur in the list can be competitors.  The
candidate must occur and must have a strictly larger count than every
different occurring value.  Thus the relation is false for the empty list
and for every tie at the maximal frequency.

Both formalizations prove the corresponding natural properties: sum and
product exist uniquely for every valid list code; greatest, least, and twice
the median exist for every valid nonempty code and are functional; and a
unique mode, whenever it exists, is functional.  Named checked regressions
record both empty folds, the four empty-list failures, a tied-mode failure,
and odd- and even-length median examples.

## Number-theoretic conventions

The nth-prime formula counts primes strictly below `p` and asserts that this
count plus one is `n`.  This avoids truncated subtraction and makes the
one-based convention, including rejection of index zero, explicit in PA.

Power is witnessed by a multiplication trace of length `k+1`, starting at one.
Prime-factor pairs are themselves ordinary two-element list codes.  Every
exponent is positive, the prime components are strictly increasing, and the
product of the certified powers is exactly the factored number.  These clauses
rule out omissions, duplicate primes, zero exponents, and alternative orders.

A digit expansion uses a Horner trace beginning at zero and repeatedly taking
`accumulator * base + nextDigit`.  Requiring a nonempty list, bounded digits,
and a nonzero leading digit except in `[0]` makes the most-significant-first
representation canonical.  A divisor list is similarly extensional: every
listed value is a positive divisor and every positive divisor occurs; strict
ordering fixes both multiplicity and order.

The checked natural properties make these specifications functional, not just
recognizers for possible witnesses.  Every positive one-based index has a
unique prime, and every prime has a unique one-based index; exponentiation has
a unique result; every nonzero natural has exactly one canonical factorization
code; each number has exactly one canonical base expansion for every base at
least two; and every positive number has exactly one canonical divisor-list
code.  The audit also records the boundary cases named above.

Here and in the preceding aggregate section, these are metatheorems about the
standard natural-number interpretation of the displayed PA formulae.  They do
not claim formal derivations, inside a PA proof calculus, of the universal
closures of every functionality and existence statement; the precise
distinction is spelled out under “What ‘represented by a PA formula’ means”
below.

## Diophantine exponentiation, tetration, and hyperoperators

In addition to the multiplication-trace PA formula in item 22, both ports
prove Matiyasevich's stronger result that the standard-natural-number graph

```text
(m, n, k) such that m = n^k
```

is Diophantine.  Here “Diophantine” has its usual single-equation meaning:
there is one integer polynomial (equivalently, an equality of two natural
polynomials) whose existential natural-number solutions are exactly the
triples in the graph.  The parameter order is result, base, exponent, and the
conventions `a^0 = 1` and `0^0 = 1` are included.

Lean specializes Mathlib's formalized Pell-equation proof of
`Dioph.pow_dioph`, exposes the binary function as a `DiophFn`, and then moves
its output to coordinate zero to obtain the three-variable graph.  Rocq uses
the independent constructive theorem `dio_fun_expo`, retains its explicit
`dio_formula`, and compiles that syntax to the official finite-vector H10
`Diophantine` interface through a single polynomial equation.  Neither port
uses the existing PA trace formula as a shortcut, and the Rocq proof does not
appeal to the generic computable-function-to-DPRM conversion.

Both ports also prove the corresponding result for natural tetration, with
the explicit convention

```text
tet(a, 0)     = 1
tet(a, h + 1) = a ^ tet(a, h).
```

Thus the result-first graph `(m, a, h)` satisfying `m = tet(a, h)` is the
existential zero set of one integer polynomial.  This is not a finite use of
closure under composition: the variable height requires a coded trace of
exactly `h` exponentiation steps.  Both developments carry the fixed base in
the injective polynomial state code `(a + x)^2 + x`, prove one encoded step
Diophantine, and eliminate the variable-length trace.

Rocq applies the independently verified `dio_rel_rel_iter` theorem from the
Undecidability library.  Lean develops the corresponding bounded-universal
elimination explicitly: Goedel-beta traces are compiled through finite
polynomial circuits and sparse radix ciphers, whose code, constant, index,
and pointwise-product certificates are themselves proved Diophantine.  The
two implementations expose both a graph theorem and an unfolded
single-equation polynomial witness contract.

Finally, both ports prove one theorem for the complete conventional
three-argument hierarchy

```text
H(0, a, b) = b + 1        H(3, a, b) = a^b
H(1, a, b) = a + b        H(4, a, b) = tet(a, b)
H(2, a, b) = a * b        H(5, a, b) = pent(a, b), ...
```

For every rank at least three, a uniform core starts with exponentiation and
obtains the next level by iteration from one.  A fixed deterministic machine
stores pending lower-rank calls in an injective polynomial stack code.  Its
four transition branches are Diophantine, its terminating run is proved to
compute the recursive hierarchy, and arbitrary finite reachability is
compiled into one existential polynomial equation.  Thus the result-first
four-variable graph `(result, rank, base, argument)` is Diophantine without
fixing the rank in advance.

## Ordinal codes below ε₀

The two ports use the same raw `ONote` hereditary-Cantor-normal-form syntax and
the same numeric code.  A raw notation is either zero or a node

```text
omega^e * (c + 1) + r,
```

where `e` and `r` are raw notations and the stored natural number `c` is the
predecessor of the positive coefficient.  Define the square-shell pairing
function by

```text
pair(a, b) = if a < b then b*b + a else a*a + a + b.
```

The shared code is exactly

```text
code(0)                         = 0
code(omega^e * (c + 1) + r)     =
  1 + pair(code(e), pair(c, code(r))).
```

The outer successor reserves zero for the zero notation, while predecessor
storage makes every displayed coefficient positive without another tag.  The
pairing function is a bijection, and both child codes of a positive node are
strictly smaller than the parent code.  Consequently the decoder is a total
course-of-values recursion, and encoding and decoding are mutually inverse on
*raw* notations and all natural numbers.  Validity is a separate guard: a node
is in normal form exactly when its exponent and remainder are recursively in
normal form and, if the remainder is nonzero, the remainder's leading exponent
is strictly smaller than the node's exponent.  Thus arbitrary natural numbers
still decode, but only normal decoded terms are ordinal codes.

Lean identifies valid codes with Mathlib's normal ordinal notations and maps a
valid code `c` to its set-theoretic denotation `denote(c)`.  Denotation is
injective on valid codes, and its range is exactly the ordinals below `ε₀`:

```text
(exists c, ValidOrdinalCode(c) and denote(c) = alpha)
  if and only if
alpha < ε₀.
```

The public arithmetic relations are guarded and result first.  `OrdinalLT(a,
b)` requires two valid inputs and compares their denotations.  `OrdinalAdd(z,
a, b)`, `OrdinalMul(z, a, b)`, and `OrdinalPow(z, a, b)` require valid `a` and
`b` and assert that `z` is the canonical code computed from them.  Their
outputs are valid and functionally unique.  Lean constructs the following
actual arithmetic semisentences and proves their standard-natural-number
evaluation specifications:

- `validOrdinalCodeFormula : ArithmeticSemisentence 1`, evaluated at `(c)`;
- `ordinalLTFormula : ArithmeticSemisentence 2`, evaluated at `(a, b)`;
- `ordinalAddFormula : ArithmeticSemisentence 3`, evaluated at `(z, a, b)`;
- `ordinalMulFormula : ArithmeticSemisentence 3`, evaluated at `(z, a, b)`; and
- `ordinalPowFormula : ArithmeticSemisentence 3`, evaluated at `(z, a, b)`.

Rocq exports the corresponding `PA.formula` values
`ValidOrdinalCodeFormula`, `OrdinalLTFormula`, `OrdinalAddFormula`,
`OrdinalMulFormula`, and `OrdinalPowFormula`, with the same parameter orders.
Its constructive extraction certificates pass the executable predicates
through closed lambda-calculus computability and the checked
model-equivalence path to a Diophantine relation.  The explicit
Diophantine-to-PA translator proves formula existence; classical epsilon is
used only at the final boundary to name one such formula.  Substitution then
normalizes unused free variables to zero, so the exported equivalences hold
for arbitrary environments, not only for specially zero-padded ones.
The focused audit shows that the raw coding and algebra theorems are closed
under the global context; the extraction/formula path records the upstream
uses of functional extensionality, proof-irrelevance-style equality of
dependent transports, classical logic, and constructive indefinite
description rather than hiding them.

The code-level algebra laws respect the noncommutativity of ordinal arithmetic.
In addition to strict-order irreflexivity, transitivity, and trichotomy on valid
codes, Lean proves associativity of addition and multiplication and the
following orientations:

```text
a * (b + c) = a*b + a*c
a^(b + c)   = a^b * a^c
(a^b)^c     = a^(b*c).
```

The first law distributes over the **right argument** of multiplication; no
commutativity or reversed distributive law is being asserted.  The last law
uses `b*c`, not `c*b`.  The zero and one laws use ordinal arithmetic's usual
conventions, including `0^0 = 1`.

Both ports' five formula-evaluation equivalences are metatheorems about the
standard natural-number model.  Lean's algebra laws additionally use its
set-theoretic denotation.  None of these statements asserts that a PA proof
calculus has derived the universally quantified validity, functionality, or
algebra statements.  Such internal PA theorems would require a separate
syntactic formalization and proof.

Rocq proves the square-shell pairing and raw encode/decode bijections directly,
then independently proves structural comparison results, recursive
normal-form invariants, preservation of normal form by its executable
arithmetic, and validity and uniqueness properties of the result-first graphs.
Its direct syntactic laws include code-level strict-order laws, zero/one
identities, associativity of addition and multiplication, the correctly
oriented distributive law `a*(b+c)=a*b+a*c`, and the exponent laws
`a^(b+c)=a^b*a^c` and `(a^b)^c=a^(b*c)`, together with `a^0=1`, `a^1=a`, and
`0^0=1`.  The proofs explicitly handle successor exponents, omega-divisible
limit parts, and finite tails.  These are proofs about hereditary normal forms.
The present Rocq ordinal modules do not define a set-theoretic ordinal
denotation and therefore do not claim the Lean theorem characterizing the
exact denotation range below `ε₀`.

## The all-permutations convention

The all-permutations predicate has four logically separate requirements:

- **soundness**: every decoded entry of the outer list is a permutation of the
  input list;
- **completeness**: every list value that is a permutation of the input occurs
  among the decoded entries;
- **exactly once**: the decoded outer list has no duplicate list values; and
- **order**: those values are sorted lexicographically.

Completeness is important: merely checking that every listed entry is a
permutation would also accept the empty outer list. It is stated extensionally
over decoded list values, rather than relying on the behavior of a particular
permutation-generating program. If the input contains repeated numbers, two
index rearrangements that produce the same list value count as the same
permutation here. Each distinct resulting list occurs exactly once. Together
with the total lexicographic order, these clauses specify the intended
canonical output independently of an enumeration algorithm. This development
represents that exact relation; a separate existence-and-uniqueness theorem for
the output of every input code is not part of the exported theorem surface.

## What “represented by a PA formula” means

Each public representation theorem exposes an actual arithmetic formula of
the appropriate arity and proves a standard-model equivalence of the form

```text
the formula is true in the standard natural-number model at parameters a
  if and only if
the corresponding guarded relation holds of a.
```

This is semantic definability in the standard model of PA, not an abbreviation
that treats an arbitrary metalevel predicate as an atomic formula. Lean uses
Foundation's arithmetic formula and definability interfaces; the Coq port uses
the PA syntax and `natModel` semantics from the repository's PA/HF
development. The Lean sequence primitives are in fact developed uniformly
over models of `IΣ₁`, and therefore apply to PA models, while the exported
external encode/decode bijection is stated over the standard natural numbers.
Both ports provide these formula-evaluation equivalences for the list,
aggregate, number-theoretic, and ordinal layers.  Rocq's separately proved
ordinal algebra has the syntactic scope described in the preceding section;
Lean additionally relates the shared codes to set-theoretic ordinals.

The headline result should not be confused with the stronger
proof-theoretic assertion that PA proves every true closed numeral instance
and proves the negation of every false instance. Such **strong
representability** requires separate syntactic derivations or a general
representability theorem. The modules here advertise standard-model formula
correctness; audit output records the precise assumptions of the exported
results.

## Formalization map

- Lean's `PAListCoding.Basic` supplies encoding, decoding, validity, and the
  round-trip/functionality results. `PAListCoding.Predicates` defines the
  guarded relations, constructs their arithmetic formulae through
  Foundation's definability infrastructure, and proves the formula-evaluation
  correctness theorems. `PAListCoding.Standard` connects the original
  relations to ordinary Lean lists, while `PAListCoding.Aggregates` proves the
  six scalar bridges, determinacy and existence properties, and edge cases.
  `PAListCoding.NumberTheory` defines the five number-theoretic relations and
  their formulae, then proves their standard interpretations and canonicality
  properties. `PAListCoding.ExponentiationDiophantine` specializes Mathlib's
  Matiyasevich theorem to the result-first `Power` graph.  The tetration
  modules build exact Goedel-beta traces, prove bounded-universal elimination
  with sparse arithmetic ciphers, and assemble the unconditional result-first
  tetration graph and its single-polynomial witness.  The hyperoperation
  modules verify a polynomial stack evaluator for all ranks at once and
  compile its finite reachability relation to the public four-variable graph.
  `PAListCoding.lean` is the public facade, and
  `PAListCoding.Audit` checks the theorem surface and its assumptions.
- Lean's `PAListCoding.EpsilonZero` supplies the shared raw notation code,
  validity, set-theoretic denotation, arithmetic graphs, and semantic
  correctness. `PAListCoding.EpsilonZeroCompleteness` proves that the valid
  denotations are exactly the ordinals below `ε₀`.
  `PAListCoding.EpsilonZeroLaws` proves the guarded order and algebra laws with
  the orientations displayed above, and `PAListCoding.EpsilonZeroFormulas`
  constructs the five PA formulae and proves their standard-model
  specifications.
- Coq's `ListCode.v` supplies the independent executable nested code and the
  metalevel meanings of the original twenty predicates. `Representability.v`
  provides compositional representation machinery over the repository's PA
  formula syntax. `ListFormulas.v` constructs the actual PA formulae and
  proves their standard-model equivalences. `NumberTheory.v` supplies the
  number-theoretic semantics and canonicality proofs, while
  `NumberTheoryFormulas.v` constructs and verifies the five additional PA
  formulae. The isolated `NumberTheoryFactorization.v` module uses MathComp's
  unbounded-primes theorem and verified fundamental theorem of arithmetic to
  provide positive-index nth-prime totality and canonical prime-factorization
  existence and uniqueness. `ExponentiationDiophantine.v` connects
  `PowerNat` to the constructive Matiyasevich formula and to the official H10
  single-equation definition; `ExponentiationDiophantineAudit.v` checks that
  result without the unrelated MathComp dependency.
  `TetrationDiophantine.v` proves the encoded-step and exact-iteration
  characterization, then compiles it to both the formula and official H10
  single-equation interfaces; `TetrationDiophantineAudit.v` is its focused
  kernel and assumption audit. `HyperoperationDiophantine.v` extends the same
  constructive method to a deterministic variable-rank evaluator;
  `HyperoperationDiophantineAudit.v` checks its graph and single-equation
  theorem. `Audit.v` checks the
  complete public surface and prints its assumptions.
- Coq's `EpsilonZero.v` implements the same square-shell/raw-notation code and
  executable structural operations. `EpsilonZeroLaws.v` gives independent
  syntactic proofs for normal forms, comparison, closure, and the core
  arithmetic laws. `EpsilonZeroPowerLaws.v` proves the full successor, sum,
  and power-of-power identities for transfinite exponentiation, including the
  fixed-limit and finite-tail decompositions used by the public code laws.
  `DiophantineFormula.v` is the explicit polynomial-to-PA translator,
  `ComputableFormula.v` connects extracted total functions to that translator,
  and `EpsilonZeroFormulas.v` exposes the five guarded public formulae.
  `EpsilonZeroAudit.v` is a focused, MathComp-independent assumption and kernel
  audit.  These modules intentionally make no claim to a Rocq set-theoretic
  ordinal model or exact denotation range.

The Lean development depends on the vendored
`lib/FormalizedFormalLogic-Foundation` project and its pinned mathlib version.
The Coq formula layer depends on `Logic/Interpretability/PAHF/Coq`; its coding
and finite-list reasoning use only the Rocq standard library.  The isolated
nth-prime totality and prime-factorization canonicality bridge additionally
requires `rocq-mathcomp-boot` version `2.5.0`; the PA formulae and their
correctness theorems do not depend on MathComp.  MathComp 2.5's released source
and opam bound target Rocq before 9.2, so the focused Rocq 9.2 ordinal and
Diophantine exponentiation, tetration, and hyperoperation audits deliberately
exclude that
unrelated bridge.

In a compatible Rocq switch, that additional package can be installed with
`opam install rocq-mathcomp-boot.2.5.0`.

## Checking

From the repository root, build the complete Lean project and run its audit:

```powershell
lake --dir Logic/PeanoArithmetic/ListCoding/Lean build
lake --dir Logic/PeanoArithmetic/ListCoding/Lean build `
  PAListCoding.ExponentiationDiophantine `
  PAListCoding.TetrationAssembly `
  PAListCoding.HyperoperationDiophantine `
  PAListCoding.EpsilonZeroFormulas
lake --dir Logic/PeanoArithmetic/ListCoding/Lean env lean `
  PAListCoding/Audit.lean
```

The root Rocq project records the authoritative source list and logical paths
for the Coq port; `rocq makefile` resolves the dependency graph. Build and
kernel-check the complete registered workspace with:

```powershell
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
```

For the focused Rocq 9.2 Diophantine and ordinal audits, build their
registered targets and then run the kernel checker.  Their dependency closures
deliberately exclude the separate MathComp factorization bridge:

```powershell
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq `
  Logic/PeanoArithmetic/ListCoding/Coq/ExponentiationDiophantineAudit.vo `
  Logic/PeanoArithmetic/ListCoding/Coq/TetrationDiophantineAudit.vo `
  Logic/PeanoArithmetic/ListCoding/Coq/HyperoperationDiophantineAudit.vo `
  Logic/PeanoArithmetic/ListCoding/Coq/EpsilonZeroAudit.vo
rocqchk -silent -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/ListCoding/Coq PAListCoding `
  -Q lib/Coq-Library-Undecidability-current/theories Undecidability `
  PAListCoding.ExponentiationDiophantineAudit
rocqchk -silent -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/ListCoding/Coq PAListCoding `
  -Q lib/Coq-Library-Undecidability-current/theories Undecidability `
  PAListCoding.TetrationDiophantineAudit
rocqchk -silent -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/ListCoding/Coq PAListCoding `
  -Q lib/Coq-Library-Undecidability-current/theories Undecidability `
  PAListCoding.HyperoperationDiophantineAudit
rocqchk -silent -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/ListCoding/Coq PAListCoding `
  -Q lib/Coq-Library-Undecidability-current/theories Undecidability `
  PAListCoding.EpsilonZeroAudit
```

The audit modules check all twenty-five list and number-theoretic
formula/correctness results together with the ordinary-list bridges, aggregate
functionality and existence properties, edge cases, and the coding existence,
decoding functionality, round-trip, and injectivity theorems.  Both ordinal
audits check the five ordinal formula specifications, guarded functionality,
and algebra laws; Lean additionally checks the exact denotation range below
`ε₀`, while Rocq independently checks its raw and syntactic surface.  The
Diophantine audits check the exponentiation, tetration, and variable-rank
hyperoperator function-graph certificates and their single-polynomial-equation
theorems.  No
generated enumeration is part of the trusted theorem boundary: the
all-permutations result is checked against its soundness, completeness,
exact-once, and lexicographic specification.

## Related research reports

Four research reports cite this project: three of the surreal collection,
two of them as a route to a further formalization and one as an engineering
pattern, and one of the research-report collection. None is formalized, and
nothing in this project depends on them.

- [`polish-models-of-omnific-arithmetic`](../../../Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic/):
  its Part VIII (batch 87, labels `pma:atr:`) **claims**, unrefereed and not
  independently reviewed, an `ATR₀` proof of Glazer's Topological
  Tennenbaum Theorem 2, using an internal MRDP theorem over
  `Q + IΔ₀ + Exp`. It contrasts that with `ExponentiationDiophantine.lean`
  here, which proves the Diophantine graph of exponentiation for the
  standard natural numbers only, and proposes one explicit `IΔ₀ + Exp`
  proof of the correctness of its Diophantine equation as a
  proof-assistant milestone. Its Part XI (batch 90, `pma:lgc:`) names this
  project for a staged formalization of its local geometric-code theorem;
  a dated note there says that the project's standard-model theorems are
  not the internal statements it needs.
- [`discrete-initial-subgroups-and-omnific-normalization`](../../../Algebra/SurrealNumbers/docs/surreal/discrete-initial-subgroups-and-omnific-normalization/):
  its source 04 (batch 90, `isg:ptg:`, residue images of nonstandard models
  of PA) read this README for its distinction between the standard-natural
  interpretation of the formulas and internally derived theorems.
- [`surreal-well-orders`](../../../Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/):
  its Part XVII (batch 97, labels `swo:hn:`) cites this README's hereditary
  Cantor-normal-form codes below `ε₀` as an engineering pattern for
  proposed modules on class-sized hereditary normal forms (`OmegaNormalForm`,
  `EpsilonTerms`). Those modules do not exist, nothing here is used by the
  report, and its theorems about proper classes are not theorems of this
  development.
- [`random-bits-arithmetic-cuts`](../../../SetTheory/Cardinals/docs/reports/ordinals-and-order-types/random-bits-arithmetic-cuts/)
  (batch 114, labels `rbc:`; AI-assisted, unrefereed, not formalized)
  studies the coding cut of a random predicate on a countable model of PA,
  the initial segment where the predicate has internal binary codes, and
  claims its almost-sure value for every independent bias law, the Boolean
  spectra of conjunction cuts and a three-regime induction theorem. Its
  proposed formalization route (Section 11) cites this README's statement
  that the project's formula evaluations are metatheorems about the
  standard natural numbers, and concludes that a theorem about arbitrary
  nonstandard models must pass through syntactic and soundness interfaces
  instead. It names no declaration of this project; the finite beta coding
  it uses as an ingredient is `finite_list_beta_code` of
  [`NotFinitelyAxiomatizable`](../NotFinitelyAxiomatizable/).
