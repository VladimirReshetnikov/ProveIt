# The source zero alias with `⊤` as truth

`PA194VerumAlias.lean` gives an explicit derivation in the native iPRA
calculus of `⊤ ↔ (⊤ → ⊤)` and a provability theorem for the standard iPRA
presentation. It also proves the corresponding classical first-order formula
in equality logic. No consistency premise is used.

This is the fixed propositional fact needed to reconcile the source identity
`I(0,0)=0` with a translation choosing `⊤` for source code zero. The existing
`PA194ZeroAlias.lean` separately proves the analogous fact in PA when truth is
chosen as `0=0`. Neither package yet connects its fixed derivation to the
numeric truth and implication codes and the represented proof compiler; in
particular neither establishes a machine-consistency implication.

Rebuild using the pinned overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-verum-alias.sh
```
