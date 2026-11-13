# Independent P13/P14 translated-consistency review

Both checked source statements use the respective `IPRAOrdinary72` or
`IPRAOrdinary72P14` positive-shifted expression. Each composes its existing
standard-iPRA `A ↔ N` endpoint with `IPRABoundedRhoZFC.zfcEquiv : T ↔ N` in
the correct orientations `A → N → T` and `T → N → A`. The resulting `T` is
the mapped Gödel–Gentzen translation of the formal ZFC consistency sentence.
The retained axiom reports for both declarations are exactly `propext`,
`Classical.choice` and `Quot.sound`.

The [checker](check.py) reran the earlier endpoint audit, verified actual
outer session 24376 exit 0, both nested exits and sampled guard records, the
source/object/log pins, the P14 provider route, all 40 direct guard slots and
2,219 overlay links. It exited 0 with [result](result.json). The checker
SHA-256 is `de6289411c8a1d4741d29488b026c74748f1a705400869317affac7787527143`;
the result SHA-256 is
`31c1f8e3d4b5387b1291b3becda58433298bb7f9bdebe78cb5d33bc9bc3e3da8`.
The first mistyped-pin refusal mentioned in the author README was reported
by the author from its terminal; no separate refusal receipt was retained,
so this review independently verifies the successful run only. The check
inherits captured-provider, sampled-monitor and external JSON/payload limits;
it is not a clean current-base reconstruction or a Lean file-semantics proof.
