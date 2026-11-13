# Same-witness eta identity

`Trace74N2EtaIdentity.graph_eta_identity` proves the following equality in the model difference ring from the same positive 74 graph zero and the explicit small-k assumption `k=8XY²+4`:

```
eta + 4Y²(2XY−(X+1)²) = 8YX+4Y+3.
```

It uses the checked graph odd-index-3 result, the third Pell ordinate formula and the canonical model-to-difference-ring map. It assumes no q≥4 bound, F/C inequality, or reverse guard.

Reviewed retry author session 49403 returned outer exit 0, with the exact named axiom report clean. Terminal `observations/attempt02/terminal.json` SHA-256 `f5eec67f4e2245833397d1cd924fa3c38d60e4d2d7ac8edec31e91773e2f6dd7`; object `/tmp/trace74-n2-eta-identity-9e2ows8i/lib/Trace74N2EtaIdentity.olean` SHA-256 `901529a57f437a838a7217970fae02c08f8001f70b83f57d204e4d3d34c6f60a`. Independent [result audit](../../reviews/trace74-n2-eta-identity-result-independent/README.md) passed, SHA-256 `a718b806c1cd9e501d81b9205b7783ea984ad1a00cbddadccf916d7d2df3005b`. Direct-pin/search-path and inherited project/package/dynamic ancestry limits remain.

Attempt01 was rejected for a late product-cast normalization error and reported `sorryAx`; attempt02 explicitly maps multiplication after unfolding. [Prelaunch](../../reviews/trace74-n2-eta-identity-prelaunch-independent/README.md) and [retry](../../reviews/trace74-n2-eta-identity-retry-independent/README.md) reviews are separate. The model-window client, runner and observations are separate work and are not covered by this identity audit.
