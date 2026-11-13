# Direct-main route: conditional model lemmas

This is an investigation of a possible further reduction of the 91-operation graph, not a 90-operation equation or an equivalence theorem. All displayed variables below are elements of an arbitrary ordered-ring structure that is a model of IΣ₁; in particular, the conclusions are not limited to the standard natural numbers. The Lean source specifies the exact model interface and hypotheses.

The 91 graph uses `X = q*w`, `Y = q³*s`, `U = Y*q²`, and a main contribution `U*(gamma+w)`. Replacing it by `U*G` for a new positive input would save its addition gate. Every old witness maps forward via `G = gamma+w`; recovering a *positive* `gamma` from a general positive `G` and `w` is not justified. This observation alone is neither a checked graph transformation nor a proof of either direction of an equivalence.

`DirectMainProjection.lean` contains three checked lemmas:

* For `a = X*Y+Y`, `c = eta+Y*k`, and `H = 3+4*a`, if `U > 0`, `Y ≥ 8`, and `k > 0`, then `H*k < U*(X+a*c)+H*(U*G+R+1)`. No split of `G` is assumed.
* Given `U > 0` and the exact root balance `U*(X+a*c)+H*(U*G+R+1) = H*(R+1+U*W)+U*main`, cancellation yields `X+a*c+H*G = main+H*W`.
* If additionally `H > 0`, `X < H`, `P < H`, and `main = P+a*c+H*t`, then the same balance implies `X = P`.

The first lemma applies the existing `ArithmeticAdaptiveMainOrientation2011.main_parts_positive` with its auxiliary `q` set to zero. The third uses the existing model-theoretic modular cancellation lemma. None of these results establishes their hypotheses from a 90-operation graph, or asserts that an iPRA proof exists.

## Verification and scope

`run.py` produced `observations/attempt01/terminal.json` and its source and stdout/stderr snapshots, with exit 0 and no warnings. The three printed Lean axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The source SHA-256 is `913b54cea53402e9da91b2fb9e5c41dbbf9e5926be9531986fc08fe90163a956`; the resulting object SHA-256 is `e2510b3deeebc7d4067710ad1f3210191e6189050a9b3bfa8641f9a9a2bf3182`. The attempt pinned and rechecked all 1,291 entries of the selected 92 halt union, and recorded resource samples. The run uses inherited package, dynamic, and source-to-object ancestry; it is not a clean closure rebuild. Its temporary provider and output paths may not persist.

## Remaining proof obligations

The existing first-factor extraction is coupled to a literal 95-graph zero and must be factored or reproved from the new graph's first residual. The new direct main residual must yield an oriented scaled norm and root balance. Existing Pell-index, index-comparison, and exact-ordinary results still consume the old literal zero or its particular signed main pair; they need appropriately generalized inputs and proofs. The Pell projection and its bounds must then be established for those new inputs. The old power-projection proof uses the original `E*q` contribution, though `X=q*w` in the 91 graph offers a direct route to the required size bound. The auxiliary residual and fixed-port conditions must also be carried through. Finally the forward witness map and the complete modified graph, including liveness and exact operation count, require graph-specific checked proofs. The checked model lemmas here discharge none of these graph-specific obligations by themselves.

`DirectMainNorm.lean` is a separately checked conditional follow-up; its precise assumptions and verification are recorded in [NORM.md](NORM.md).
