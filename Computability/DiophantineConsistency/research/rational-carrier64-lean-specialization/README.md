# Rational specialization of the literal 64/65 identity

For any four **integer** ports `p` with `p 0 ≠ 0` and any integer
14-coordinate valuation `v`, the checked theorem `rational_value_eq`
identifies the 64-row rational evaluation using the fixed leaves

```
Urank = (p 3 : ℚ) / (p 0 : ℚ)
Wrank = (p 2 : ℚ) - (p 3 : ℚ)
```

with the rational cast of `Carrier65.value p v`. The checked theorem
`rational_zero_iff` derives the corresponding zero iff, and
`positive_zero_iff` quantifies over all **strictly positive integer**
valuations. Both directions use exactly the same valuation. This is a
Lean-level identity and existential equivalence for arbitrary integer
ports satisfying nonzero beta; it does not itself instantiate the
actual ports or prove an iPRA endpoint.

The fixed rational `Urank` is not an added quantified input, but may be
nonintegral. This does not produce a 64-operation integer-leaf equation
and does not alter the maintained 65-operation equation or its PDF.
The two symbolic ring assumptions from the prerequisite packet are
discharged by rational division and subtraction; integer cast injectivity
gives the zero iff. The actual ports' nonzero beta and connection to an
iPRA provider must be supplied separately. In particular, identical
module names do not establish provider coherence.

## Evidence

Attempt02 passed: Lean exit 0, no warnings or `sorryAx`; each of the three
axiom reports is `[propext, Classical.choice, Quot.sound]`. The guarded
run used `-M2400`, 120 seconds, sampled 3.5 GiB process-group RSS and
10 GiB minimum available-memory limits, nice 19, and idle I/O. It took
1.633 seconds, peak sampled RSS 1,974,018,048 bytes, with stable direct
guards. The successful object is
`/tmp/rational-carrier64-specialization-priority-check02/RationalCarrier64Specialization.olean`,
SHA-256 `15f3ac6c4c29c8a71d0ebad456c58f2592c59407660b08a11a90ff1ac063fea8`.

Directly guarded providers are the checked predecessor
`/tmp/rational-carrier64-identity-priority-check03/RationalCarrier64.olean`,
SHA-256 `a2aa0510f8dc710e455981b605c304c2a0dbfe75e343d443f33eac27aeef8b43`,
and `Mathlib/Data/Rat/Cast/Lemmas.olean`, SHA-256
`c1e2ff937444031d0fcb29196353fb43c62c75960ed0e1e00788af13cf8ec579`.
Transitive and dynamic provider ancestry is inherited from that previous
check; its Carrier65 object resolved through an existing object in another
worktree. This is not a new source-closure rebuild.

Attempt01 failed because type inference selected the rational graph before
the intended integer-to-rational cast; its source, compiler log and receipt
are retained in `observations/attempt01`. Attempt02's source snapshot, log
and receipt are retained in `observations/attempt02`.

| Artifact | SHA-256 |
| --- | --- |
| `RationalCarrier64Specialization.lean` | `cdf5cf2d40c3f143dc12a286e8c5968602360cd2ea0e08c593168211e755071f` |
| `check02.py` | `bee197f34f4df1689888e77b534fc0c0f65d1d1b39dbcb5ffac3b3ed9aa42cd6` |
| `observations/attempt02/compile.log` | `a25238f8e48ca68092967d55ab3917344dd330b6c89b17922332b311eb8158bf` |
| `observations/attempt02/result.json` | `289a0493d7ccc0ef785c325153b135bb851dcbbe30d3430a93113ab3638b3acf` |
