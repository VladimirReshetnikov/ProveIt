# Composing the two independent 108-operation reductions

The exact checker `../verification/round12_1980_certificate.py` verifies the
composed certificate: 107 arithmetic instructions, comprising 59
multiplications and 48 additions, with 34 positive unknowns and 22 equations.
The seven fixed-numeral instructions give 114 under that convention.
This note records why the two mathematical reductions may be composed.

Use the input-unit homogeneous index of `INPUT_UNIT_PROOF.md`, including its
fixed scale and the special unit target. Apply both replacements:

1. As in `POSITIVE_COEFFICIENT_BOUND_PROOF.md`, use the bound
   `Y+alpha=q^2`, where `Y=ell+eq`, and the positive witness
   `Omega=Z*lambda-2e`. Compute `S3=B*lambda*(1+q)-Omega*C^2` and retain
   the positive witness `sigma=S3`.
2. As in `PELL_ODD_ROOT_PROOF.md`, use `Q=UM^2`, the norm
   `tau*(tau+1)=Q*(Q+1)*k^2`, and the index equation `k=r+1+h*Q`.

For soundness, the positive-coefficient proof's initial bounds use only the
coding equations and the two positive witnesses. They give `C<q^2`, valid
packing blocks, and `r>=n>=8` without invoking any Pell equation or decoding.
Those facts are exactly the preliminary bounds needed by the odd-root proof.
Its positive interval and signed Pell argument force the first Pell index
to equal `r+1`. Hence `h` is even, and the positive witnesses
`tau_old=2*tau+1` and `h_old=h/2` restore the previous first Pell equations.
Every coding witness, including `Omega`, `sigma`, and the size slack, is
preserved by this restoration.

The full positive-coefficient proof now applies to the restored system. Its
Pell argument recovers `q=B^L`, then strengthens `C<q^2` to `C<q` before
decoding. The first-block borrow vanishes, the high mask forces the packed
quotient to be canonical, and the homogeneous target tests recover the unit
digit and the original quadratic equations. Thus the composed system is sound.

For necessity, start with the positive witnesses supplied by the input-unit
construction. The positive-coefficient replacement changes only the size
slack and adds `Omega`. The odd-root replacement changes only the first Pell
root and its index quotient. Their forward witness maps therefore commute,
and all resulting system unknowns are positive.

The first reduction removes one addition from the 109-operation schedule;
the second removes one multiplication from a disjoint part of that schedule.
The composed checker does not infer its count merely by subtraction: it
verifies every one of the 107 primitive identities, all 22 source residuals,
the two triangular corrections, and the exact polynomial witness maps.
It retains all fixed-index, domain, and support metadata in its JSON receipt.
These are a mathematical equivalence proof and an exact arithmetic
certificate, with no new Lean formalization or optimality claim.
