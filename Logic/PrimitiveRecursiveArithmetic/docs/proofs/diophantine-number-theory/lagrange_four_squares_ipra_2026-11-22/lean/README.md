# Lean formalization scaffold

## Exact status

`FourSquares.lean` is a **source-level formalization scaffold**. No Lean executable
was available in the producing environment, so this file was **not elaborated,
compiled, or kernel checked**. Its mathematical definitions were aligned with the
separately tested Python implementation, but Python testing is not Lean checking.

The source provides total definitions and proposed Lean proofs of the generic
iteration lemmas and final conditional assembly. It has no admitted theorem or
axiom declaration. Its six unfinished arithmetic claims are explicit fields of
`ArithmeticContracts`, which is a structure of hypotheses, **not** an instance
asserted to exist. In particular,

```lean
theorem lagrange_from_contracts (C : ArithmeticContracts) (n : Nat) :
    ∃ a b c d : Nat, n = a*a+b*b+c*c+d*d
```

is a conditional assembly statement. Removing the argument `C` requires proving
and constructing every field of that structure. `OBLIGATIONS.md` identifies those
proofs and their dependencies.

This is stronger than a prose list of theorem names, because the representation,
searches, branch choices, loop clocks, invariants, and target terms are defined.
It is not represented as a completed formal proof.

## Program definitions

The code uses the standard Hamilton quaternion multiplication, with descent
product `Z4.mul x (Z4.conj r)`. Its four coordinates are integers solely for
convenient host notation. `normSq` is the sum of their squares.

The search `firstLt test B` scans the finite interval `[0,B)`, returning the first
successful index or the sentinel `B`. `primeB` is a Boolean trial-divisibility
test; its propositional wrapper is `IsPrime`. It does not rely on an imported
classical field, prime factorization theorem, or `Nat.Prime` API.

`seedState p` treats `p = 2` directly. For an odd prime it searches
`((p-1)/2+1)^2` ordered pairs and produces a representation of `m*p` with
`0 < m < p`. Nonprime inputs also have total defined outputs; no correctness
property is promised for their purported prime representations.

`descentStep` has an absorbing branch for `m ≤ 1`. For positive even `m` it
chooses one of three coordinate pairings and halves the pairwise sums and
differences. For odd `m > 1`, it uses centered residues, Hamilton multiplication,
and exact coordinate division. The program executes **exactly `p` steps** in
`primeRep p`.

`factorStep` removes the least divisor at least two from the remaining positive
integer and multiplies its prime representation into the accumulated vector.
`signedFourSquares n` uses **exactly `n` steps**, with a direct zero case.
`fourSquares n` takes the four absolute values. The Python implementation may
omit already absorbing iterations for speed; its `literal_clock` mode follows
the Lean clocks exactly.

## From this scaffold to host Lean correctness

1. In a Lean 4 installation, run `lean FourSquares.lean`. No Mathlib imports are
   required for the present scaffold. Fix any elaboration/API differences and
   record the exact compiler version. This package does not claim compatibility
   with a particular untested release.
2. Prove finite-search correctness and the local arithmetic lemmas in
   `OBLIGATIONS.md`. Mathlib may be used for convenient host arithmetic tactics,
   provided the arithmetic proof is also traced to the iPRA derivation described
   in the report.
3. Construct `completedArithmetic : ArithmeticContracts` using those lemmas.
4. Specialize `fourSquares_correct completedArithmetic n` and
   `lagrange_from_contracts completedArithmetic n`.
5. Add a bridge theorem relating `IsPrime` to `Nat.Prime` only if interoperability
   with external Mathlib developments is desired. The proof here needs only the
   bounded definition already supplied.

The host proof can use Lean's generic induction principle to assemble a lemma for
arbitrary predicates. For the iPRA result, the actual instantiated induction
formulas must be the quantifier-free formulas listed in the report. An arbitrary
Lean induction proof does not establish that restriction on its own.

## From host correctness to an object-theory iPRA proof

The desired mathematical result is an iPRA proof of the open identity

```text
F0(n)^2 + F1(n)^2 + F2(n)^2 + F3(n)^2 = n,
```

where `Fi` are the four explicitly defined primitive recursive coordinate
functions. The existential theorem then follows by existential introduction and
universal generalization in intuitionistic first-order logic.

To formalize that meta-level claim, use a syntax and derivation checker for iPRA:

* Terms contain variables, zero, successor, and symbols for a fixed finite family
  of primitive recursive functions, closed under the definitions actually used.
* Formulas use equality and the intuitionistic first-order connectives and
  quantifiers. Order, divisibility, primality, and all bounded quantifiers are
  abbreviations implemented by primitive recursive Boolean characteristic
  functions; they are not extra induction schemes.
* Nonlogical axioms are the successor axioms, defining equations for each
  primitive recursive function, and quantifier-free induction with parameters.
* The logical rules are those of intuitionistic first-order logic with equality.
  Equality and all Boolean tests on natural codes are decidable constructively.

Replace the host types as follows:

| Host object | First-order natural-number implementation |
| --- | --- |
| `Int` | Canonical zigzag code: `2z` for `z ≥ 0`, `2(-z)-1` for `z < 0` |
| `Z4`, `DescentState`, `FactorState` | Fixed-arity nested natural pairing |
| Integer addition/multiplication/negation | Case splits on code parity, with natural arithmetic |
| Euclidean division/remainder | Bounded quotient search, with a fixed total zero-divisor default |
| `allLt` and `firstLt` | Primitive recursion over a supplied natural bound |
| `iterate` | Primitive recursion on the explicit `p` or `n` clock |
| `PrimeState`, `FactorInvariant` | Equations and decidable order tests on primitive recursive terms |
| Finite universal statements | An equation asserting that a Boolean prefix fold is `true` |

No universal primitive recursive evaluator is needed or assumed: each function
in this fixed program receives its own defining equations. A total uniform
interpreter for all primitive recursive programs must not be silently assumed
primitive recursive.

For each finite arithmetic identity, prove the corresponding encoded identity
by quantifier-free induction and elementary equational reasoning. For each
bounded search, prove its Boolean prefix invariant by quantifier-free induction.
For each clocked loop, instantiate the generic preservation and saturated-rank
arguments with the encoded quantifier-free invariant. Combine the resulting
object-theory derivations in the same dependency order as the host proof.

This final syntax-level derivation and its kernel-checked translation into iPRA
are **not** supplied in the present scaffold. The report supplies the complete
human-readable argument and the restriction audit; the files here make the
remaining formalization work concrete and reviewable.

## Definition map

| Mathematical component | Lean identifier |
| --- | --- |
| Bounded conjunction/search | `allLt`, `firstLt` |
| Primality test and least divisor | `primeB`, `IsPrime`, `leastDivisor` |
| Signed quadruple and norm | `Z4`, `Z4.normSq` |
| Euler identity polynomial | `Z4.mul`, `Z4.conj` |
| Centered residues | `centered`, `centered4` |
| Even multiplier reduction | `halfPairs`, `evenHalf` |
| Initial prime multiple | `seedState` |
| Prime descent transition | `descentStep` |
| Prime descent invariant/rank | `PrimeState`, `descentRank` |
| Fixed clock iteration | `iterate` |
| Prime representation | `primeRep` |
| General factor transition | `factorStep` |
| General invariant/rank | `FactorInvariant`, `factorRank` |
| Natural coordinate witness | `fourSquares` |
| Unfinished arithmetic interface | `ArithmeticContracts` |
| Conditional universal equality | `fourSquares_correct` |
| Conditional existential theorem | `lagrange_from_contracts` |

