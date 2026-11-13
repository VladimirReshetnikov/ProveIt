# Fresh-base comparison of the 66/138 and 67/106 graphs

`Unscaled66Vs106Fresh.lean` checks that, for the same valuation in every model of IΣ₁, the positive-shifted 66-operation degree-138 expression has an internal zero exactly when the positive-shifted 67-operation degree-106 expression does. Both use `CurrentWindowCarry2011.ports`. The result composes the checked fresh-base same-zero theorems, with no additional assumptions on the valuation. This is a model-level comparison; it is not a new independent rebuild of the underlying base or a separate iPRA theorem.

The file also proves an identity in every commutative ring. With `A = P*Q*W`, `Z = strong`, `G = V²−y²`, and `D = delta`, it is

```
unscaledValue − value106 = −D*A*Z*(Z−1)*G.
```

Consequently the values agree on the strong-norm-one locus. The all-model zero equivalence is established separately via their respective equivalences with the 65-operation expression; it does not assume the strong-norm-one locus as a hypothesis.

## Check and provenance

Run `python3 -I -S -B check01.py` from any directory when its fixed `/tmp` output path does not exist and the stated inputs are present. The recorded attempt used Lean `-M2800`, one worker, nice 19 and idle I/O, with a 120-second limit, sampled process-group RSS stop of 3.5 GiB and host available-memory stop of 10 GiB. `attempt01/result.json` records Lean exit 0, stable 337 direct/companion/shadow guard slots and PASS, with 10 RSS samples and no stop. `attempt01/outer-observation.json` separately records the actual terminal exit 0 for session 95783. The log has no warnings or `sorryAx` and reports `[propext, Quot.sound]` for the ring identity and `[propext, Classical.choice, Quot.sound]` for the model theorem. The output object is `/tmp/current2011-unscaled66-vs106-fresh-priority-check01/Unscaled66Vs106Fresh.olean`, SHA-256 `4eafb3349a554d7ac322280a50e8d163020be24147d83af603c0dfd470547a42`.

The direct clients are the fresh-base `Current2011Unscaled66Fresh.olean` (`43de05d18c2854a224ebcd01c560cb5327752118ee08164277f38e7611a01b00`) and `FreshModel106.olean` (`d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942`). Their source and state hashes and their recorded dependency/companion/shadow slots are checked before and after. This does not provide a dynamic trace of every transitive load, and the resource guard on this run does not retroactively apply to either producer. The extension-build state records an initial final-client failure; the separate corrected `FreshModel106` client passed and its own direct provider checks were retained. No historical-stage provider is deliberately added to this run's search path.

The operation counts and degrees are supplied by the separately audited graph certificates, rather than proved by this Lean file. The maintained 65/150 PDF is unchanged.
