# One common bound for a family of first-index witnesses

The sources are `PRAFstIdxFamilyBound.lean` and `PRAFstIdxFamilyBoundChecks.lean`. The author build passed, authenticating 81 unchanged local source/object parents in an overlay of the local `fstIdxDef` bound author provider and the independently accepted PR-fold provider. The local bound has been independently accepted. Private replay `/tmp/pra-fstidx-family-independent-_v2kv_0_` and root replay `/tmp/pra-fstidx-family-independent-rl6i2tv5` both passed with all source, object and complete-log hashes matching the author; both terminal states and author/root source snapshots and logs are recorded. Foundation and Mathlib are inherited.

For arbitrary candidate-PRA models, `modelFstIdxFoldBound` states that one primitive-recursive fold bounds the syntactic witnesses of the actual mapped `fstIdxDef(x,p)` for every `p < k`. It composes the local `p+1` bound, the fold and monotonicity of `bnd`. It does not bound the enclosing proof predicate or prove Foundation's ZFC refutation bound certificate.

Replay with:

```sh
python3 Computability/DiophantineConsistency/reviews/pra-fstidx-family-author-replay/replay-combined.py \
  --local /tmp/pra-fstidx-bound-2qkpaz2k/lib \
  --fold /tmp/pra-witness-fold-independent-euvu7ykv/lib
```
