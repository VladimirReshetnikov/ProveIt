# Independent review of scaled coefficient-power reuse

**PASS; no requested change.** I read the complete frozen helper and companion, authenticated the author trio and inert dependencies, and independently reconstructed all four complete source arrays. The one-multiplication saving is valid on identical supplied coordinates over every commutative ring.

Reviewed author pins:

| File | SHA-256 |
|---|---|
| matrix193_scaled_power_reuse.py | `2186513567e31204f78726d856686be2818205638563e9b1cfa052b382177942` |
| matrix193_scaled_power_reuse.json | `c81bb0ef774361b1b8b4f1b6084ec90329f9c0e22665d8968ced5517959de2b4` |
| matrix193_scaled_power_reuse.md | `39114f292022ef9bd6dbd5065eed34c5634b77e4050556faa69ae2f656d466b8` |

The fresh [independent checker](review_matrix193_scaled_power_checks.py), SHA-256 `370be252f0ffef9eceae914abf3704471d3187babb9586c1c3a607a4c7fa6925`, and its [receipt](review_matrix193_scaled_power_checks.json), SHA-256 `b9701c53e2f0408938427af29799146eac37d3da5b60b96b6211544657c5d60f`, record all seven author/parent/map pins. No author or predecessor Python was imported or executed during this review.

The independent reconstruction directly edits the authenticated parent rows: delete private `cp344`, move the already-paid `cp400` immediately before `cp345`, and replace that target by `cp317*cp400`. In the three chart listings, `cp333` also occurs later and is moved before `cp400`; the baseline already computes it early enough. Literal sequential checks authenticate all operands. This explicit reconstruction agrees with every one of the author's6,024 rows, not merely the changed rows or counts.

Fresh expansion gives `cp317=Q^150`, `cp333=10Q^12`, `cp400=−20Q^12`, `cp344=Q^162`, and the old and new `cp345=−20Q^162`. The removed wire's only consumer is the replaced target. All other retained definitions are literal. Substituting this polynomial identity at the actual paid Q therefore proves the entire output identity by induction through the complete graph. This does not require Q to be nonzero, positive or a history scale. I also read the author's complete input-bound cut interpreter; its scope matches this argument.

All retained pure-Q values and all sixteen full coefficient words agree. Every552-row coefficient component is reconstructed, all source rows and supplied ports are live, and the complete finalizers are traced through their actual residual squares and sum trees with unchanged native multiplier and private consumer boundary. Fresh full counts are1,509 /1,506 /1,506 /1,503, with one fewer multiplication and unchanged additions per array.

Witnesses, ordinary input, fixed ports and output are unchanged. Exact degrees35,587 /53,345 /53,347 /71,105 transfer from the immediate terminal-power parents through full polynomial equality on identical variables. This review makes no new native/compiler proof or accepting-trajectory claim. The earlier terminal-carry and IDLE comparisons remain ordinary-input projection statements; the author correctly does not strengthen those older inverses or claim an improved universal84 bound.

Fresh normal and optimized exact replays of the independent checker from `/` pass:

```sh
review_wip=/absolute/path/to/native-stream-queue
python3 "$review_wip/review_matrix193_scaled_power_checks.py" \
  --root "$review_wip" --expect "$review_wip/review_matrix193_scaled_power_checks.json"
python3 -O "$review_wip/review_matrix193_scaled_power_checks.py" \
  --root "$review_wip" --expect "$review_wip/review_matrix193_scaled_power_checks.json"
```

For the author trio in another directory, supply `--author-root /absolute/author/directory`; it defaults to `--root`. The checker has strict duplicate/nonfinite JSON rejection and recursive type-exact receipt equality.
