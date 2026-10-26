# Fresh algebraic simplification opportunities

Snapshot: `8e8b5dcb954969621c484588f0b902be1cfea7b3`.
All source paths below are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.
No repository sources were changed. The novelty-audit agent checked the two
loose ZIPs and the previously placed report linked from `docs/incoming`.

## 1. Carry signed congruences as a relation, rather than reopening signs

### Concrete current burden

`NativePellStepDown.lean`, `index_residues`, lines 101–125, transports
`u ≡ ±J`, `u ≡ (−1)^h s`, and `c | s−p ∨ c | s+p`. The proof
constructs a separate congruence disjunction, then proves a local
`hJp_of_sign` by four branches, explicitly assembling divisibility witnesses
`k1−k2` or `−k1−k2`. `signed_index_residues`, lines 147–157,
then splits the sign of `V` again to transport `V.natAbs`. The final
`eq_of_residues` at lines 161–174 removes the sign using positive
half-modulus bounds.

### Mechanism

Define

    PMModEq m a b := a ≡ b [ZMOD m] ∨ a ≡ −b [ZMOD m].

This is an equivalence relation. Negating either argument preserves it.
`PMModEq m |a| a` follows from the sign cases of integer absolute value.
Keep the Pell-specific facts in this relation until the final
half-modulus representative is selected:

    PMModEq m u J
    PMModEq m u s
    PMModEq m s p
    --------------------------------
    PMModEq m J p.

The proof is two transitivity applications and one symmetry application.
The existing `neg_one_pow_eq_or` is used only once to introduce the middle
signed relation, rather than propagated through every downstream case.
An adapter converts the relation to the existing divisibility disjunction,
so public theorem statements can remain unchanged.

The positive-half representative theorem is mathematically immediate:
if `0<a,b`, `2a<m`, `2b<m`, then `PMModEq m a b` iff `a=b`.
For the plus branch, the difference has absolute value less than `m`;
for the minus branch, `0<a+b<m`, so it cannot be divisible by `m`.
The current `eq_of_residues` already supplies this arithmetic.

### Checked artifact

`algebra_prototypes/SignOrbit.lean` imports only `Init`. It proves the
equivalence/negation laws for an arbitrary relation preserved by an
involution, **and concretely instantiates that relation for integers as
`a % m = b % m`**. The theorem `int_residue_transport` is the exact integer
sign-composition statement, and `int_natAbs_transport` handles the natural
absolute-value representative. These are not merely propositional
placeholders with the desired conclusion assumed.

Checked successfully using the existing Lean 4.32.0 compiler. The log is
`algebra_prototypes/SignOrbit.check.log`. Four generic results have no axioms;
the integer instance and two integer transports use only `propext` (from
core integer remainder lemmas). There is no `sorry`, `axiom`, or
`native_decide` in the module. This is a standalone check; integrating it
into the project's import graph and checking the rewritten Pell theorem
remain separate work.

### Scope and a necessary guard

This simplifies sign bookkeeping, not Pell classification or the
`step_down` theorem. In particular, **do not infer `PMModEq m a b` from
`a² ≡ b² (mod m)`**. The implication fails for composite moduli: modulo 8,
`1² ≡ 3²`, but 1 is congruent to neither 3 nor −3. Retain the existing
Pell step-down result which actually supplies the signed index residues.

The present prototype has generic infrastructure cost, so its line count is
not a measured net reduction of the project. The immediate target is the
25-line sign block plus the repeated 11-line absolute-value transport;
future signed Pell arguments amortize the interface.

Novelty finding: none of the three audited proposal packets introduces a
signed-congruence orbit relation. Earlier Pell advice was to decode source
register equations once; this operates strictly later in the arithmetic
proof.

## 2. Closed form and exact ambiguity classification for cyclic carries

### Current code and why this is a research option

`NativeCyclicCarry.lean` defines a monotone update on the bounded carry box
and obtains a least fixed point in `exists_bounded_carries` (lines 37–47).
That existence proof is already short and works for an arbitrary
predecessor map. `NativeCyclicCarryWord.lean` proves conservation of the
packed word and excludes the two zero-residue digit representatives using a
strict positive target. The proposal below is special to an actual cycle.
Its benefit is a canonical formula, equality of independently constructed
normalizations, and a complete uniqueness criterion. **It should not be
advertised as an immediate shortening of the existing short general
existence proof.**

### Statement

Let `ρ>1`, `n>0`, and let `a_i∈N` be indexed cyclically modulo `n`.
Set

    M = ρ^n − 1,
    A_i = Σ_{j=0}^{n−1} ρ^(n−1−j) a_(i−j),
    k_i^- = (A_i − 1) / M,
    k_i^+ = A_i / M.

The subtraction in the formula for `k^-` is **natural truncated
subtraction**. Then both arrays satisfy

    k_i = floor((a_i + k_(i−1))/ρ).

Every nonnegative solution of this recurrence lies between `k^-` and `k^+`
pointwise. More precisely:

1. If `a` is identically zero, the only nonnegative solution is zero.
2. If `a` is nonzero and some `A_i` is not divisible by `M`, the solution
   is unique and `k^-=k^+`.
3. If `a` is nonzero and every `A_i` is divisible by `M`, exactly two
   solutions exist: `k^-` and `k^+=k^-+1`. Their normalized digit arrays
   are respectively the constant arrays `ρ−1` and 0.

Under the current budget

    a_i + D < (D+1)ρ

the least formula satisfies `k_i^-≤D`.

### Complete ordinary proof

**Geometric identity.** Reindex the finite cyclic sum. It telescopes to

    ρ A_i = M a_i + A_(i−1).                 (1)

All weights are positive. Consequently, either every `A_i=0` (exactly when
all raw digits vanish), or every `A_i>0`.

**Greatest formula solves the recurrence.** Write

    A_i = M k_i^+ + e_i,  0≤e_i<M.

Substitution into (1) gives, over the integers,

    M(a_i+k_(i−1)^+−ρk_i^+) = ρe_i−e_(i−1).

The right side is strictly greater than `−M` and strictly less than `ρM`.
The factor in parentheses is an integer, hence it lies in `[0,ρ−1]`.
Thus it is the actual Euclidean remainder of `a_i+k_(i−1)^+` on division
by `ρ`; the quotient is `k_i^+`.

**Least formula solves the recurrence.** If all `A_i=0`, it is zero and
the claim is immediate. Otherwise write

    A_i = M k_i^- + e_i,  1≤e_i≤M.

This is the positive-remainder convention, equivalent to
`k_i^-=(A_i−1)/M`. Equation (1) gives the same integer equality. The
right side now lies between `ρ−M` and `ρM−1`, still strictly between
`−M` and `ρM`. Thus the same quotient/remainder conclusion follows.

**Exhaustiveness.** For an arbitrary fixed point, let

    d_i = a_i+k_(i−1)−ρk_i,  0≤d_i<ρ.

Multiply each local equality by the corresponding geometric weight and
sum around the cycle. The carry terms telescope exactly:

    A_i = M k_i + D_i,
    D_i = Σ_{j=0}^{n−1}ρ^(n−1−j)d_(i−j),
    0≤D_i≤M.                                (2)

If `A_i` is not divisible by `M`, (2) forces
`k_i=floor(A_i/M)`, and therefore determines the entire cyclic carry
array by propagating the recurrence forward from that coordinate. If
`A_i` is divisible by `M`, then `D_i` is 0 or `M`. The first case forces
every digit to be 0; the second forces every digit to be `ρ−1`, since all
weights are strictly positive and each digit is bounded by `ρ−1`.
Equation (2) then determines globally `k^+` or `k^-`, respectively.
If all `A_i=0`, nonnegativity in (2) forces `k=0`. This proves the full
classification without needing a separate coprimality argument.

**Budget.** The integer form of the budget is

    a_i ≤ (D+1)(ρ−1).

Summing the geometric envelope gives `A_i≤(D+1)M`.
If `A_i>0`, then `A_i−1<(D+1)M`, so `(A_i−1)/M≤D`.
The zero case is immediate. The subtraction of one matters: if every
`a_i=(D+1)(ρ−1)`, then `k^-` is constantly `D`, while `k^+` is
constantly `D+1` and does not fit the current box.

**Strict transport specialization.** In the indexing convention above,
`A_(n−1)=Σ_{i<n} a_iρ^i`, the ordinary packed raw word. If this word is
congruent to `F` modulo `M`, with `0<F<M`, then it is not divisible by
`M`. The normalization is therefore unique. This gives a natural
`existsUnique_normalization` wrapper for the strict transport theorem.
It can identify independent witness constructions without carrying
arbitrary choices through every subsequent theorem.

### Validation and limits

`algebra_prototypes/check_cyclic_carries.py` independently compares the
formula to monotone iteration from zero on 57,540 instances: radix 2–5,
cycle length 1–4, bound 0–2, and every raw array satisfying the numerical
budget. It also enumerates every candidate fixed point in the box
`0..D+1` for 2,323 smaller instances, agreeing exactly with the two-formula
classification. Results are in `cyclic_carry_checks.json`.

This is finite experimental validation in addition to the complete ordinary
proof above; the closed-form theorem has **not** been formalized in Lean.
The stated box includes every possible fixed point in these cases by (2),
but the Python experiment itself is not a proof of that universal fact.

The algorithm is not intended as a fast evaluator for enormous encoded
words: its direct implementation costs O(n²) scalar arithmetic and builds
large integers. The proposal concerns proof interfaces and canonical
uniqueness. A linear-time recurrence for `A_i` is possible after one initial
sum, but no runtime improvement is claimed here.

Novelty finding: none of the three audited packets contains the explicit
cyclic formula or the exact two-solution classification. One prior packet
explicitly advises leaving the existing monotone fixed-point existence
proof alone. The proposed use respects that recommendation: retain the
general existence lemma and add a specialized canonicality theorem only
where downstream witness equalities justify it.

## Optional further direction: cyclic packing as an algebra homomorphism

The novelty audit also found no discussion of this, but it is less immediate
than the two proposals above and need not be a headline recommendation.
`NativeCyclicConvolution.word_convolution` proves multiplicativity by
several finite-sum reindexings; `NativeCyclicRotation.word_rotate` repeats
the exponent-period/reindexing argument, and carry conservation repeats its
linear consequences. Their common source is the evaluation homomorphism
from the additive monoid algebra `N[ZMod n]` to `ZMod (ρ^n−1)`, taking a
basis monomial at `i` to `ρ^i.val`. The relation `ρ^n=1` makes this map
well defined. Dense arrays remain the public interface, with a private
equivalence to finitely supported functions. Then convolution is product,
rotation is multiplication by a basis monomial, and packing is evaluation.

`map_mul` gives **congruence**, not equality of natural packed words.
The existing strict bounds are still needed to recover exact equality.
The up-front typeclass/coercion burden may outweigh the present savings;
adopt only if further convolution identities accumulate. This is distinct
from the prior generic semiring DAG-compiler proposal, which concerns gate
semantics rather than cyclic word packing.
