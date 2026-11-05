# Independent source and mathematical review: sign33 draft

Reviewed `research/nine-sharing-sign33-signs-draft/Sign33Draft.lean`, SHA-256 `c6cf5a3c39c00188050a71f5a7e95d93884344db9b275bc095b224527a49fb4d`, against `ArithmeticPellFirstIndex.lean`, SHA-256 `8cf79ed14f00f565accbfae0eb03ccacca597d06d12a509fecd6d3272e30f9ce`, and `ArithmeticPellRecurrence.lean`, SHA-256 `63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16`. The original presence-only checker ran successfully and reproduced its recorded result; it does not check Lean syntax or proofs.

The `windows_from_maintained_norms` statement reproduces the positive-input hypotheses, fixed-port inequalities, transport equation and all four norm equations of `maintained_first_indices`. The call supplies the original `i`: the maintained theorem itself defines `I = delta a*i*c*c`. It is not the alternative ordinary-index theorem, where the `i` argument must instead be scaled. `scalar_window` supplies its truncated-natural gap and `R+2 < w*s*q^4`; the displayed identity `w*s*q^4 = (w*q)*(s*q^3)` gives `R+2 < E`. The maintained theorem explicitly supplies `2*R<c`. The uncompiled proof's inference and elaboration remain unchecked.

The five intended sign consequences are mathematically valid under the stated intermediate bounds:

* With `q≥1`, `F+alpha≤q`, and `alpha≥0`, the product `(q−1)*(q−F)+alpha` is nonnegative. With `E≥0`, `N≥1`, `k≥0`, and `r≤E`, `E*N+k−r ≥ E*(N−1) ≥ 0`.
* With `c>0`, `T≥1`, `2r<c`, put `u=c*T−r`. Then `2u−c>0`, so `u>0` and `u>c/2`. If `f≥2`, then `f²≥4`, hence `f²*u−c>0`.
* If `S>0`, `y≥1`, and `S²*(V²−y²)+y²=1`, then `V²−y²≤0`: a positive difference would give a positive first term while `y²≥1`.
* In the natural-model strong norm, `delta a=(a+1)(a+3)>0` and `i,c>0`; consequently `f²>1`. Discreteness together with `f>0` yields `f≥2`. The draft's natural-model theorem explicitly assumes the strong norm and all positivity needed for this argument.

These statements use distinct natural-model and ordered-ring signatures. This review does **not** establish their connection. In particular, the transport gap is truncated subtraction in the model whereas the sign lemmas use ring subtraction; the actual finite fixed-port bounds and casts, model positivity and `absdiff`-square identity must still be linked to the five literal sign33 seed norms. One must also construct the nonnegative model-natural witnesses and prove both directions of the all-model zero bridge before any Jones or iPRA claim. No Lean process was run; mathematical inspection does not validate tactic scripts, elaboration, provider resolution or the proposed theorem as a compiled Lean result.
