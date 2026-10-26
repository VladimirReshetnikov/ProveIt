# LTE divisibility spectrum as the organizing theorem

## Contribution and novelty boundary

The exclusion audit found no previous LTE, valuation-spectrum, or prime-power-order proposal in the 23 research packets a-w and the five incoming archives. This proposal concerns a new theorem interface and a reorganization of the existing `PrimePowerOrder` proofs. The mathematical content is a standard consequence of lifting the exponent, not a claim of new number theory.

Reviewed source: `Computability/DiophantineConsistency/Lean/DiophantineConsistency/PrimePowerOrder.lean`, commit `9f35798db4a63c25e435fca14d75931144657d7e`.

The current direction is:

1. Compute an exact valuation only for exponents `p^k`.
2. Separate `k=0` from `k+1`.
3. Invoke the prime-power order criterion in the successor branch.

The proposed direction proves the complete divisibility predicate first:

    p^(k+1) divides g^m-1  iff  p^k divides m.

Here `m` is arbitrary, including zero. Exact valuation at `m=p^k` and exact multiplicative order are then short corollaries. This changes the mathematical interface, rather than hiding the case split in a tactic.

## Exact hypotheses and proof

Let `p` be an odd prime and `g` a natural number. Assume `p` divides `g-1`, while `p^2` does not divide `g-1`. No extra unit or positivity premise is introduced.

The second assumption already forces `1<g`: if `g<=1`, natural subtraction gives `g-1=0`, divisible by every number. The first assumption then shows `p` does not divide `g`. These are the existing two helper theorems; they remain unchanged.

Let `v_p` take values in extended natural numbers, with `v_p(0)=infinity`. The exact-lift assumptions give `v_p(g-1)=1`. Mathlib's existing `Nat.emultiplicity_pow_sub_pow` therefore gives, for every natural `m`,

    v_p(g^m-1) = 1 + v_p(m).

Now use `pow_dvd_iff_le_emultiplicity` on both sides:

    p^(k+1) | g^m-1
    iff k+1 <= 1+v_p(m)
    iff k <= v_p(m)
    iff p^k | m.

Cancellation of the finite summand 1 in extended naturals is justified by `ENat.add_le_add_iff_left`. Infinity is retained, so `m=0` does not require an exceptional branch.

The existing natural-to-`ZMod` bridge turns this into

    (g : ZMod (p^(k+1)))^m = 1  iff  p^k | m.

By `orderOf_dvd_iff_pow_eq_one`, the left predicate is exactly `orderOf g | m`. Evaluate the equivalence once at `m=p^k` and once at `m=orderOf g`. The two resulting divisibilities give equality by `Nat.dvd_antisymm`. The modulus `p` (`k=0`) is included in the same proof.

The former `exact_lift` theorem is the specialization `m=p^k` at levels `k` and `k+1`; simplification with `Nat.pow_dvd_pow_iff_le_right hp.one_lt` proves it directly.

## Files

- `FullLTESpectrum.lean`: standalone prototype, preserving the three existing prerequisite helpers and adding the full divisibility theorem, the optional modular-power interface, the order theorem, and boundary examples.
- `candidate/DiophantineConsistency/PrimePowerOrder.lean`: complete same-module replacement. All six existing theorem signatures are unchanged. Only the new `lift_dvd_iff` interface is added; the optional standalone modular-power convenience theorem is not added to production.
- `prime-power-spectrum.patch`: reviewable diff against the pinned source.
- `metrics.json`: whole-module and proof-body source counts, hashes, and a declaration-signature comparison.
- `verify_lte.py`: read-only replay against an ordinary checkout with the pinned toolchain and Mathlib dependencies installed. It compiles the candidate into a temporary directory and then runs the maintained `PrimePowerOrderChecks.lean` against that candidate.
- Validation logs and `validation.json`: exact checked scope and axiom comparison.

## Validation scope and limits

The standalone prototype and concrete replacement are checked by Lean 4.32.0 with Mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`. The missing Mathlib `NumberTheory.Multiplicity` module was compiled locally from that revision, with unchanged cached prerequisites. No project source is modified by this packet.

The maintained `PrimePowerOrderChecks.lean` supplies controls for the base modulus, a nontrivial power, arbitrary `k`, natural subtraction at `g=0` and `g=1`, the invalid even-prime extension, the invalid higher initial valuation, and modulus zero in the generic cast bridge. Additional standalone examples exercise exponent zero and exponents 18 and 6 modulo 27, which are not both powers of the prime.

The odd-prime assumption must remain: for `p=2`, `g=3`, `k=2`, `m=2`, one has `8 | 3^2-1` but `4` does not divide `2`. The exact first lift must also remain: `g=10` is already 1 modulo 9.

The complete production module shrinks from 80 to 75 physical lines, counting the added helper, its declaration, and its documentation. The old `exact_lift` proof body shrinks from 9 lines to 1, and `order_succ` from 16 to 4. All six pre-existing theorem signatures are textually unchanged.

No whole-project build or performance improvement is claimed. The source reduction is modest once the stronger helper's complete declaration and proof are counted. The principal benefit is a more useful rewrite interface and removal of a proof branch.

## Primary references

- Maintained module: https://github.com/VladimirReshetnikov/ProveIt/blob/9f35798db4a63c25e435fca14d75931144657d7e/Computability/DiophantineConsistency/Lean/DiophantineConsistency/PrimePowerOrder.lean
- Maintained checks: https://github.com/VladimirReshetnikov/ProveIt/blob/9f35798db4a63c25e435fca14d75931144657d7e/Computability/DiophantineConsistency/Lean/DiophantineConsistency/PrimePowerOrderChecks.lean
- Literal-controller caller: https://github.com/VladimirReshetnikov/ProveIt/blob/9f35798db4a63c25e435fca14d75931144657d7e/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentAuxiliaryOrder2011.lean
- Mathlib LTE: https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/NumberTheory/Multiplicity.lean
- Mathlib divisibility and multiplicity: https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/RingTheory/Multiplicity.lean
- Mathlib extended-natural cancellation: https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Data/ENat/Basic.lean
