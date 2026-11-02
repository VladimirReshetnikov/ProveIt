# Square-divisor witness in IΣ₁ models

[`ModelSquareDivisor.lean`](ModelSquareDivisor.lean) proves a natural
square-divisor witness in every model supported by the existing
`ArithmeticGcdNormalization` interface. For model elements `a,b,r,t`, if
there is a four-natural Bézout certificate for `a,b` and

```
t*(b*b) = r*(a*a)+(b*b),
```

then there is a model element `s` satisfying `r=(b*b)*s`. No positivity
or nonzero hypothesis is needed; the separate `zero_right_edge` theorem
confirms that when `b=0` the hypotheses force `r=0`.

The first lemma explicitly squares the supplied signed Bézout certificate to
obtain a certificate for `a,b*b`. The norm gives `b*b ∣ r*(a*a)` using
`bez_divisor`; two uses of `unit_certificate_cancel` remove the factors of
`a`. These two existing APIs operate on model naturals and four-natural
certificates. The proof does not import a difference ring or assume unique
factorization. The theorem provides a natural `s` by model divisibility; it
does not yet give a primitive-recursive term for `s` in object-level iPRA.

## Paired bounded replay

The source was compiled separately against the author and peer outputs of the
matched 70-module coherent source-current parent. The suffix replay ran
`lean -M4000 -j1` with a 180-second bound per child, checked its three axiom
reports, queried direct imports, and re-ran the full parent comparator before
and after. The two resulting suffix objects and stdout reports matched by hash.
The actual wrapper session 18427 exited 0; its output and receipt hash are
recorded in [`terminal-observation.json`](terminal-observation.json). The
[receipt](replay-receipt.json) retains both process results, commands, object
hashes, direct import observations, and pinned parent data. Both reports for
the main lemmas and the zero edge list only `propext`, `Classical.choice`,
and `Quot.sound`; these are Lean metatheory axioms, not object-theory iPRA
axioms.

To replay when the pinned temporary providers still exist, invoke

```
python3 -I -S replay.py --output /tmp/ipra-model-square-divisor-replay-NEW
```

The [parent pair](../../../reviews/ordinary12-coexistence-pair-independent-audit/README.md)
and this [paired suffix](../../../reviews/ordinary12-model-square-divisor-independent-audit/README.md)
have each passed an independent artifact audit. The suffix audit rechecks
the recorded objects and inputs; it is not a further Lean recompilation.
The parent inherits package-transitive and dynamic
loading ancestry, and the Foundation provider's outer wrapper exit remains
unobserved. The replay's checks are point-in-time checks, not protection
against changes between observations.

After the paired build, `origin/main` was merged at commit
`a6a58953ac17ba2e02a418e2c3d1064db73e00ad`. Its project Lean diff adds
`ArithmeticOddOrdinateResidue.lean` and `ModelThirteenRestoration.lean`.
A separate point-in-time [source recheck](source-recheck-after-merge.json)
compared all 70 files in the pinned manifest with their workspace bytes and
found no drift. It does not compile or audit the newly added modules.

This is a **model-level theorem**, not an internal iPRA proof. It assumes the
reduced norm and Bézout certificate rather than constructing them. The full
integrality descent, its termination and object-theory encoding, application
to the signed graph and its polarized residual, compact44 checker
calibration, and the final 12-variable equivalence remain open.
