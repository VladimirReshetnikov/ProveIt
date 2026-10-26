# Actual controller positions: independent Lean review

PASS, 2026-10-26. Reviewer: `controller_certificate`; author:
`complemented47_review`. I read all 178 main lines, all 48 check lines, the
complete author receipt, and the relevant finite-data and generic cardinality
interfaces before replay. No correction is requested. I did not author this
packet or `CurrentControllerData2011`; I authored the indirect kernel
dependency. This is a review of the new position geometry, not a fresh audit
of the complete imported closure.

| Frozen input | SHA256 |
|---|---|
| `CurrentControllerPositions2011.lean` | `aab00b74d13e24bb78dda62c5c5a5fa55990f414821fef7b56d02c8fee675acf` |
| `CurrentControllerPositions2011Checks.lean` | `7723e5c1bd82e7711aa47930c219ff967ae3e0de8e9b180db85aa431c55f84ea` |
| `CurrentControllerData2011.lean` | `a86aa5cc6b523bd659df8681012a1a39307ea340c27a7785629d30699ca151ae` |

For p=120199, T=p^k and N=p^(k+1), the literal natural position is
`2+(p-1)*j.val`, where j belongs to `ZMod T`. The proof starts from the
canonical bound `j.val+1<=T`, multiplies by p-1, and obtains the
subtraction-free budget `position+T+p<=N+3`. This is sufficient for
`position+1<N`, including k=0. The separate truncated-subtraction upper bound
is valid at k=0 but need not be sharp there; the focused check correctly
computes the sole orbit position as2, and the author receipt explicitly
identifies the truncation.

Injectivity follows from positivity of p-1 and injectivity of canonical
values. Optional position3 is distinct because the progression starts at2
and every positive step is at least2. The cast into ZMod N has exactly its
natural value by the strict upper bound, so both cyclic injectivity and
disjointness from optional cell3 are proved without an unproved no-wrap
identification.

For every `rw<k`, `p^rw<T` and the same budget prove the temporal safety
condition `position+p^rw<N`. The optional cell3 has both safety bounds as
well. These arguments do not require the stronger cardinality-size condition
`d*p<T` used by the separate controller subset theorem. The k=0 embedding
statements remain valid; no rw satisfies the temporal theorem's explicit
`rw<0` hypothesis.

`support` inserts optional3 exactly when epsilon is nonzero. Its membership
and safety theorems are valid even for arbitrary epsilon; the exact count
`s.card+epsilon` correctly requires `epsilon<=1`. Cardinality first uses
injectivity of the progression and then its disjointness from3. The natural
support-to-cyclic-support cast is injective on the actual finite support
because every member is strictly below N, so the cyclic count is preserved.
Finally `cyclicSupport_safe` exports the actual canonical-value conclusions
`0<j.val`, `j.val+1<N`, and `j.val+p^rw<N`, precisely the two bounds consumed by
the independently built dummy-safety theorem. No dummy value, F increment,
rank equation, unit, orbit equivalence, or native calibration is assumed.

The checks cover k=0, empty subsets, optional3, cyclic injectivity, the exact
cardinality, and unreduced successor inequalities. All 13 printed axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The new
files contain no additional axiom, `sorry`, or unsafe evaluator.

Both sources were freshly compiled with Lean4.32.0, `-M6000 -j1`, and their
`Elab.async false` setting. The overlay
`/tmp/current-controller-positions2011-controller-peer/lib` excluded both
reviewed stems initially and was prepended to LEAN_PATH after `lake env`
initialization. The main and checks output only into that overlay; the checks
therefore imported the freshly compiled main. Existing prerequisite objects
were reused, with no full dependency rebuild claim.

Both runs passed without warnings or errors. Main: 8.60 seconds and 3,266,076 KB
peak RSS. Checks: 3.24 seconds and 3,234,036 KB. Both output objects are
byte-identical to the authors' frozen objects. All 10 pinned source, object,
toolchain, and author-receipt inputs remained unchanged after both replays.

| Replay artifact | SHA256 |
|---|---|
| Main object | `fb7b49a7b537aa728eed0f9654fd509d9b1efa3eda45d9ae46c94286db9885f6` |
| Checks object | `d7b503222a725e5536572f3bee3532e86b30959d53d41ce4a6ff707c4df183d7` |
| `main.log` | `3410b7797694c9c7f512d1f3c10a497ec35cc8c5b4adf334799e5f47ea94bce0` |
| `checks.log` | `91c7de19c84f54ddf0c72a94ebfc458a723475724be911b8138e6a2d0859661b` |
| `inputs-before.json` | `c67a4da83890a61957636ce216d9c9bac8a0ef41c99eab3685a4670699251093` |

No reviewed source, accepted object, shared document, or Git state was edited.
The packet establishes physical placement, safety, and cardinality. A separate
finite-support word-mutation construction is still required to turn these
positions into accumulated ordinary C/F changes and a prescribed rank residue.
