# Guard-free carrier residue

For the same positive 74 graph zero, positive beta, positive valuation and model assumptions as `Trace74CarrierBound`, `Trace74CarrierResidue.graph_carrier_h_divides_HDB` proves signed difference-ring divisibility `h ∣ H D B`. It uses the carrier-root factor to write `Z=h D H z`, then the explicit `Z` expression. The generic commutative-ring identity `reduce_carrier_mod_h` and the graph specialization `graph_explicit_carrier_residue` reduce it modulo `h`, using `q=h+1`, to

```
h ∣ (4s(w+1)−1) w s ((K0+w)C−F),    h=beta J.
```

The coefficient is 4: the actual register is `H=4*Am1−1`. The signed `B` is `(K0+w)C−F`. All three assertions apply to the same p/v graph witness; no reverse guard, F/C bound or coprimality is assumed.

Author attempt02 passed in actual tool session 99436, outer exit 0, with all three named axiom reports clean. Its terminal `observations/attempt02/terminal.json` SHA-256 is `45150d255e3dd399840d561432479130f1121bf8fb2ac7859e8190e9407201d7`, and object `/tmp/trace74-carrier-residue-wa9r48nz/lib/Trace74CarrierResidue.olean` SHA-256 is `0740d7e62dfa1fd7e836a2664025d9ef23d52cba689df7af846f5e1f07b35fae`. Independent [result audit](../../reviews/trace74-carrier-residue-result-independent/README.md) passed, SHA-256 `a106c06387974f096aea70c8b2d7707dc0e164ba4ea0beb2034dd9ab01edd168`. Direct-pin/search-path and inherited project/package/dynamic ancestry limits remain. Earlier attempt01 was rejected for a synthetic-coordinate elaboration error; its graph-specialization report contained `sorryAx`. Attempt02 corrected that coordinate proof.

The product condition by itself does not imply `h|B`: take the actual `beta>1`, `J=1`, `w=beta`, `s=1`, `C=1`, and `F=K0+w−1`. Then the leading product is divisible by `h=beta` while `B=1` is not. This is merely an algebraic scalar assignment satisfying positivity when `K0>0`; it does not assert the other graph factors or a full zero. Stronger graph constraints might still force a suitable coprimality or `h|B` by another route.

[Source review](../../reviews/trace74-carrier-residue-draft-independent/README.md), [prelaunch review](../../reviews/trace74-carrier-residue-prelaunch-independent/README.md), and [retry prelaunch review](../../reviews/trace74-carrier-residue-retry-prelaunch-independent/README.md) are recorded separately.
