# A finite candidate-PRA checker for a single target h1 leaf

`check : Code 1` checks a newly defined one-leaf certificate, encoded using
Foundation pairing as `pair 2 (pair a b)`. For that tag it returns one plus
the theorem number produced by the fixed PA194 target h1 generator; for every
other tag it returns zero. This certificate encoding is an independent choice,
not an identification with the upstream multi-rule checker's encoding.

`check_correct` proves, in every candidate-PRA model with an IΣ₁ arithmetic
reduct, that `check c = y+1` if and only if `Head1Certificate c y`. Its proof
uses the model's actual pairing projections, so both fields and the certificate
may be nonstandard. The preceding `pa194-target-head1-standard` package
separately proves that the fixed theorem generator produces an actual PA194 h1
axiom on standard inputs. This standard binding does not replace the all-model
checker proof.

The checker handles only h1 leaves. It does not validate modus ponens,
generalization, other axiom schemas, or arbitrary proof trees. It is not yet a
port or replacement of the complete upstream multi-rule checker, and it does
not prove the source compiler, PA calibration, or a machine reduction.

The final module passed a fresh Lean 4.32 suffix build against the retained h1,
standard binding, source-inversion, target-compiler, project and Foundation
overlays. The printed main theorem axiom dependencies are `[propext,
Classical.choice, Quot.sound]`, without `sorryAx`. A full nested replay using
the script below is pending.

From the repository root, using matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-target-head1-checker/check.sh
```

The script rebuilds the prerequisite chain under `/dev/shm` by default; set
`TMPDIR` for another suitable temporary directory.
