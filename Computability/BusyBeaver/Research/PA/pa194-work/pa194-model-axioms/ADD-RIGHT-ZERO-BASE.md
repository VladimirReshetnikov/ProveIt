# Addition right-zero ordinal-induction base

The sources define the typed right-zero property and construct its actual Foundation ordinal-induction base from source equality. They use the checked zero-input addition law and the empty-order-isomorphism theorem; neither a canonical empty representative nor raw object equality of arbitrary empty objects is assumed. The successor case, full right-zero theorem, addition-commutativity bridge, `sM3` and native iPRA transfer remain open.

From the repository root with a fresh output:

```bash
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-add-right-zero-base.sh "$PWD" /dev/shm/pa194-add-right-zero-base-repo
```

This incremental replay rebuilds two local sources, rejects `sorryAx`, and checks three axiom reports, retaining repository `m1`/empty-isomorphism and older addition-zero-law/Foundation objects. The older lower addition dependency provenance is separately under review.
