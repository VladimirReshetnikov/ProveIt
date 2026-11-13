# Guard-independent signed rank/main-index congruence

`Trace74SignedRankMain.graph_signed_rank_main` proves that the same positive 74 graph zero has a signed rank representation `R=ι rp−ι rn` and an odd main Pell ordinate `c=y_r(A−1)` with r≥3 such that

```
SignMod c (absdiff rp rn) r.
```

The result combines the audited signed-rank auxiliary theorem with the guard-free Fold witness and existing `rank_to_main_index`. Their auxiliary and Fold indices are not assumed equal. `absdiff rp rn` is the model magnitude of the signed difference; this theorem does not prove R≥0, a magnitude window, an individual F/C bound, the reverse guard, or an equation/iPRA endpoint.

The reviewed author check passed in actual session 96895, outer exit 0, with its single named axiom report clean. Terminal `observations/attempt01/terminal.json` SHA-256 `0ed186d552d5a5979b452d3affa06eb770226ee740005aeb43b45d08b747fbeb`; object `/tmp/trace74-signed-rank-main-4whcfs88/lib/Trace74SignedRankMain.olean` SHA-256 `71b6172e5acdc2751bb2c0a012bd78cfec6f80faddcc135030b0b7d04f16c2dd`. Independent [result audit](../../reviews/trace74-signed-rank-main-result-independent/README.md) passed, SHA-256 `ce6a28d53f99a37b6668117496e20f05d877b9bf6dd4b21a612ec228da0677b0`. Direct-pin/search-path and inherited project/package/dynamic ancestry limits remain.

[Source review](../../reviews/trace74-signed-rank-main-source-independent/README.md) and [prelaunch review](../../reviews/trace74-signed-rank-main-prelaunch-independent/README.md) are separately recorded.
