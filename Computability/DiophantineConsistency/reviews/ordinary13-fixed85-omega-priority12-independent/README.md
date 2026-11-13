# Independent review: priority 1–2 fixed85 Omega alternatives

This review covers only the five priority 1–2 modules in the pinned hazard packet. An independent line-diff check confirms that their original source bytes change only at the ten identified `omega` proof sites and the added `Mathlib.Tactic.Ring` / `Mathlib.Tactic.NormNum` imports. All namespaces and declarations, including hypotheses and conclusions, therefore remain textually unchanged. It reproduces the author's receipt and checks the selected modules' local lexical reverse dependencies.

The arithmetic substitutions match their surrounding hypotheses:

* In each of the two exact-index clients, the two shifted inputs are at least one, and their strict sum bound gives `q≥3` by discreteness.
* In `ResidueRankLower`, the same gap gives `q≥3`; the already established truncated-subtraction cancellation yields `q-1≥2`, while `alpha<q-F` and `alpha≥1` yield `q-F≥2`. Hence the first rank factor is at least five. From `q²≥9` and the separately justified subtraction cancellation, the second factor is at least eight; the existing proof combines them to get 40.
* In `Residue90FyForce`, the shifted eta contribution and the positive `Y*k` contribution are each at least one, so their sum is at least two.
* In `AQ17Forced105Arithmetic`, the first replacement uses `q≥1` to derive `y²≤q*y²` and contradicts the strict inequality obtained from its zero-ordinate equation. The second uses nonzero z to obtain `z²≥1`; with `q≥4` and the explicit equation `q*z²=1`, it derives the contradiction `4≤1`.

These are source-level mathematical checks. The proposed proof terms and even the preexisting hypotheses that supply the facts have not been elaborated or provider-audited. The snapshots have different basenames while retaining the original logical namespaces; they do **not** rewire any imports. A future overlay would need to select exactly one provider per original module and rebuild all affected reverse consumers against coherent dependencies. This review does not establish that such a build works, that the separate missing `Mathlib.Tactic.Omega` import is repaired, or that the fixed85 endpoint or PDF is proved. The other three alternatives in the packet are outside this review.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-fixed85-omega-priority12-independent/check.py | cmp - reviews/ordinary13-fixed85-omega-priority12-independent/receipt.json
```

No Lean build, staging or provider change was performed.
