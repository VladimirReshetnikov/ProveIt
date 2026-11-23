# Elementary chapter: formalization blueprint

## Status

`ElementaryDefinitions.lean` contains total semantic definitions and no admitted theorem declarations. It is an **uncompiled outline**, because this workspace has no Lean executable. The chapter contains complete human proofs; `elementary_manifest.json` states every theorem's clock, dependencies, semantic target, and object-theory proof obligations. These are not represented as completed Lean proofs.

A complete formalization has two obligations. First, show in Lean that the explicitly defined algorithms have the claimed mathematical specifications. Second, construct derivations in the chosen syntax of intuitionistic PRA. The first obligation alone would not establish the second. In particular, importing Mathlib and applying a theorem about `Nat.Prime`, `Finset`, or `Nat.gcd` does not by itself certify an iPRA proof.

## Semantic data and definitions

The provided definitions cover the following data:

- `DivState`, `divStep`, and `divide`: quotient and remainder from a counter with clock `a`.
- `EuclidState`, `euclidStep`, `extendedEuclid`, and `gcdPR`: two remainders and a signed 2-by-2 coefficient matrix, with clock `a+b+1`.
- `dividesB`, `primeB`, `leastFactor`, `FactorState`, `factorStep`, `factors`, and `valuation`: decidable arithmetic predicates, bounded divisor search, prime lists, and bounded exponents.
- `congruentB`, `coprimeB`, `phi`, `crtCheckB`, `crtWitness`, and `orderWitness`: finite residue calculations. `crtWitness` is deliberately a bounded scan below the product; the human proof also supplies the faster merging construction.
- `sigmaPow`, `tau`, `sigma`, `mobius`, `liouville`, `squarefreeB`, `squarefreePart`, and `squarePartRoot`: all arithmetic functions used in the chapter, including explicit square-root witnesses for the parity characterizations.
- `sieveStep` and `sieve`: the actual crossing-off sieve with a finite Boolean list.
- `paddedDigits`, `digitSum`, `CarryState`, `carryStep`, and `carryCount`: all finite digit and carry data used by Legendre, Lucas, and Kummer.
- `convolution`: a semantic schema for each fixed pair of primitive recursive functions. A single object-language theorem instead receives coded finite integer tables as inputs.

The semantic convenience `choose := Nat.choose` should be replaced, or shown equal, to the Pascal-table implementation when quoting the algorithm into iPRA. Its defining recurrence is

- `C(0,0)=1`, `C(0,k+1)=0`;
- `C(n+1,0)=1`, `C(n+1,k+1)=C(n,k)+C(n,k+1)`;
- entries beyond row length are zero.

A row of length `n+1`, with entries bounded by `2^n`, supplies a primitive recursive code.

## Core proof statements

Use `P` as a convenient Lean proposition only after establishing that it is the truth condition of a primitive recursive Boolean. For object induction, use the corresponding Boolean equality, not arbitrary Lean induction over `P`.

1. **Division.** For `0 < b`, induction on the clock proves `i = b*s.q + s.r`, `s.r < b`, `s.q <= i`, and `s.r <= i`. Both branches of `divStep` are linear arithmetic. Derive uniqueness separately from `q<q'`, `q=q'`, `q'>q`.
2. **Extended Euclid.** For `s := iterate euclidStep i initial`, preserve `s.x = s.u*a+s.v*b` and `s.y = s.r*a+s.s*b` in signed arithmetic. For each fixed natural `d`, preserve the equivalence between `d|a and d|b` and `d|s.x and d|s.y`. Preserve `s.y=0 or s.y+i<=b`; this implies zero second remainder at `a+b+1`. Bound each coefficient magnitude by `(a+b+2)^i`.
3. **Factorization.** Preserve `remainder * product(factors) = n`, primality and sortedness of the recorded prefix, and `remainder>1 -> remainder+i<=n`. The final product is `n`. For uniqueness, compare two sorted lists by a bounded cancellation loop. Do not invoke strong induction over an unbounded existential factorization predicate.
4. **Valuations.** Identify the bounded maximum `valuation p n` with the number of occurrences of `p` in the canonical factor list. Concatenation proves additivity. Construct divisibility, gcd, and lcm witnesses by subtracting, minimizing, or maximizing exponent arrays.
5. **Finite residues.** Bézout supplies a bounded inverse. Verify the residue permutation and its inverse pointwise. Product preservation can be a separate finite-array swap lemma. Euler, Fermat, order, Wilson, and RSA then follow by the chapter's displayed calculations.
6. **CRT.** Prove the two-modulus solver first. Iterate for coprime lists. For general lists, form maximal prime-power constraints, selecting a least index attaining each maximal exponent; bounded pairwise compatibility proves every constraint is respected. The existence proof also certifies that the finite search `crtWitness` succeeds and returns a value below the lcm.
7. **Finite polynomial arithmetic.** Encode a coefficient array of known degree, with integer coefficients. Prove addition, convolution multiplication, and the binomial expansion by loop invariants. Prime divisibility of inner coefficients proves Frobenius. Lucas uses coefficient comparison with the unique base-p digit tuple. Kummer uses a separate invariant for the digit addition state; summing the local equations telescopes the carry difference.
8. **Arithmetic functions.** Establish the divisor/exponent-tuple bijection. Then all product formulas, parity statements, and multiplicativity claims are finite reindexings. Möbius cancellation is an explicit involution; convolution associativity is a finite triple-sum reindexing. The bounded Möbius theorem uses only indices at most the supplied `N`.
9. **Perfect numbers.** Build the witness `e := valuation 2 N + 1`. The proof uses equality of positive finite sums and the explicit three-divisor contradiction. It does not require a statement about all odd perfect numbers.

## Quoting these proofs into iPRA

Choose the concrete language and proof calculus already used by the report. Each data constructor is replaced by its natural-number tuple or finite-array code. Integer arithmetic is represented by sign/magnitude or an equivalent canonical pair code. Every function used above is either a basic arithmetic function, a composition, or a supplied-clock primitive recursion. Bounded searches fold a success flag and first witness through the range; they are not unbounded minimizations.

For each loop, generate a quantifier-free invariant `I(inputs,i,state_i)=1`. A bounded universal assertion such as “all earlier entries are prime” becomes the equality to one of an explicit Boolean conjunction fold. Prove its initial value and its preservation as object derivations, then instantiate the quantifier-free induction rule. Decode the final state and discharge the theorem's positivity antecedents. Unbounded universal quantifiers in the theorem statement are introduced only after the input parameters have been arbitrary throughout the derivation.

For any temporary code bound, one may use the displayed rectangular encoding: an array of length `L` with entries below `B` has a code below `B^L`, together with its length and base. Lists of integers use a natural signed encoding and a bound on absolute values. Larger intermediate expressions are bounded by finite maxima of the explicitly fixed primitive recursive functions over the relevant input rectangle. This does not require a total evaluator for arbitrary primitive recursive program codes.

The pinned ProveIt snapshot already supplies potential foundational adapters in `Derivations/Lean/IPRADerivations/Core/Division.lean`, `Gcd.lean`, `Bezout.lean`, `EuclidLemma.lean`, `Search.lean`, `Permutation.lean`, `Pigeonhole.lean`, and `Descent.lean`. Before importing them, compare each exported statement and representation with these specifications. Their presence is a reuse opportunity; this package does not claim that the current outline has been linked to or compiled against those modules.

## Completion order and acceptance criteria

Complete division and signed arithmetic first; then Euclid, factorization, valuations, and finite permutation/reindexing lemmas. Proceed to CRT and the finite modular theorems, followed by factorial/digit results and arithmetic functions. For every theorem in the JSON ledger, retain both the semantic theorem and the generated object derivation, and run the actual proof checker on that derivation. A clean build should contain no `sorry` or new axiom, and a successful object proof check must be reported separately from the Lean semantic build. Finite numerical tests are useful regression checks, not replacements for either proof obligation.
