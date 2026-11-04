# Independent source review: signed rank congruence

No mathematical blocker was found in unchecked `research/trace74-signed-rank-congruence-draft/Trace74SignedRankCongruence.lean`, SHA-256 `6663031030a63a1cce44cea143c5801457912316441ac4a6a68ba2d2475398da`. No Lean was run.

The helper uses the model's two division-with-remainder decompositions and equality of remainders to derive `(ι d) | (ι x−ι y)` in the difference ring. The graph client obtains the positive first Pell index n, its actual ordinate and `k mod q⁴=(2n) mod q⁴` from the accepted first-index theorem. It applies the helper with those same n and p/v, and separately uses the accepted signed offset divisibility `q⁴|e` at the same p/v. The actual register identity `e=k−rank−1` yields `rank+1−2n=(k−2n)−e`, hence the advertised signed divisibility. The offset theorem uses no independently chosen n, so the proof does not conflate existential witnesses.

The theorem assumes positive beta, positive original 74 valuation and its actual 74 zero. It does not require the synthetic old coordinate positive, or infer a natural rank representative, rank bound, fixed-port guard, graph equivalence or iPRA result. Tactic elaboration and selected compatible provider ancestry remain to be checked.
