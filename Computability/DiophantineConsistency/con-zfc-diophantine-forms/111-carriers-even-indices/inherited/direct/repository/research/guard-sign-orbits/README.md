# Two exact private sign orbits

This research packet proves that two more guards can be supplied
existentially after a literal affine change of private coordinates.
It takes the frozen102-guard973-integer family as input. It does not
materialize a new quartic or claim a new projected-variable count.

The two guarded values are raw645/contracted295(shared.Zminus1) and
raw655/contracted301(shared_index.U). All other100 guarded values are
fixed by both maps, as are all643 original semantic-prefix coordinates.
Thus the argument changes private certificates and preserves the
encoded arithmetic inputs and outputs.

`CERTIFICATE.json` records both complete affine maps and one sign for
each of the1177 raw rows and585 contracted rows. `check.py` independently
substitutes into every whole polynomial. It also verifies the involution
identities, commutativity, every guard-domain condition, all1259 raw
restoration commutations and the exact nine-row bootstrap-norm ideal.
No bounded test is used to establish the following universal proof.

## 1. Negating the comparison unit

Let U=raw655. Negate U, the common B quotient/raw658 and all15 actual
S quotients:

    raw688,724,792,838,874,904,947,977,1007,1037,1067,1097,1127,1157,1187.

Leave every other raw coordinate fixed. The complete finite certificate
verifies the following facts directly from all original rows:

* U appears only in its square or in a product with one of those16
  quotients, so every such product and U squared is unchanged.
* Each flipped quotient has no unmatched use elsewhere. Every raw row
  and every contracted row is exactly invariant, coefficient for
  coefficient.
* All these quotients already range over unrestricted integers and
  none is among the current102 guarded values. The other101 guard
  values are unchanged.
* The map is an involution and fixes every semantic-prefix coordinate.

Apply this involution iff U<0. The resulting U is nonnegative. No claim
U>=A or natural interpretation of a quotient is used to justify this
normalization. If U=0, no change is needed for the guard sign. The
actual unit equation and later positive V bounds can be used only after
the normal-domain hypotheses for the frozen theorem have been supplied.

This directly preserves each equation `B=A+U*bq` and `S=X+U*Sq`, as
well as the actual norm. In particular, it does not negate an S or R
comparison root or change a power-congruence numerator.

## 2. Reflecting the bootstrap witness

Write z0=raw645, Z=raw646 and L=raw648. Their actual defining rows are

    Z=1+z0,  L=W*Z,

with W=raw643. Use the affine involution

    z0 -> -z0-2,  Z -> -Z,  L -> -L,

and fix all other raw coordinates. The complete row identities verify
that only raw rows594 and596 change sign. Every other raw row is
unchanged. On the667-coordinate equation, raw646 is an omitted affine
wire; the corresponding map is just

    contracted295 -> -contracted295-2,
    contracted296 -> -contracted296.

Only contracted row244 changes sign. Thus every row zero and the entire
sum of squared body rows are preserved. Every other101 guarded value
is fixed.

The potentially exceptional case z0=-1 must be excluded before claiming
the new z0 nonnegative. Retain the actual t0/raw0 and T/raw694 guards.
The unchanged four original-row bounds, proved before any semantic
interpretation, give A/raw644>=2. An exact original-row ideal combination
expands the bootstrap norm as

    A^2-1-W^3*(W+2)*Z^2 =0.

No sign of W is needed here. If Z=0, this gives A squared=1, whereas
A>=2 gives A squared-1>0. The checker proves the strict last inequality
by shifting A=a+2, yielding `a^2+4a+3`. Consequently Z is nonzero and
z0=-1 is impossible at a zero of the actual rows.

If z0>=0, leave it fixed. Otherwise the integer z0 is at most-2; apply
the reflection and obtain `-z0-2>=0`. This preserves all equations and
every other guarded value. Merely invoking the symmetry of a squared
witness without excluding Z=0 would have been insufficient.

## 3. Composition and existence statement

The two affine maps commute. The checker verifies this on their entire
support and checks that each of the1259 raw restoring polynomials
commutes with the corresponding contracted map. There is no implicit
assumption that an integer affine restoration preserves naturalness.

Suppose the667-coordinate body has an integer zero with only the100
remaining guard equations. Restore the raw tuple over Z using the
already certified592 affine recipes. Apply the original t0/T bounds,
then apply the two branch-dependent involutions above. All100 currently
guarded body values stay fixed, so their original guard witnesses can
be retained. Both omitted private guard values are now nonnegative.

Restrict to the667 contracted coordinates. The full585 row identities
give another zero of the same original body. Choose two Legendre guard
triples for the two normalized values and place their six integer
witnesses in the exact missing slots of the frozen102-guard973 system.
They are850,851,852 for contracted295 and853,854,855 for contracted301;
the certificate records and verifies these exact slot triples.
This produces an actual literal973 zero. Conversely, any literal973
zero restricts by forgetting these two triples. Hence the100-guard
specification and the frozen102-guard equation have equivalent integer
zero existence.

The five pointwise sign consequences and the frozen988/994 ordinary
normalization can now be applied **after** this orbit normalization,
through the literal973 bridge. Their hypotheses have not been applied
to a tuple while its U or bootstrap-witness guard was still absent.
In particular, this proof does not silently reuse a natural Pell
criterion on signed U data.

The100-guard specification would have667+300=967 integer unknowns and
585+100=685 quadratic rows. This is a specification-level count, not a
new optimized endpoint: this packet stores the symmetry and domain
certificates only, without the new whole polynomial coefficient files
or projection certificates. No new679-variable frontier claim is made.

## Reproduction and scope

From the repository root:

```sh
python3 -B Computability/DiophantineConsistency/research/guard-sign-orbits/generate.py --check
python3 -B Computability/DiophantineConsistency/research/guard-sign-orbits/check.py
python3 -B -O Computability/DiophantineConsistency/research/guard-sign-orbits/generate.py --check
python3 -B -O Computability/DiophantineConsistency/research/guard-sign-orbits/check.py
```

Negative controls reject an omitted U partner flip, wrong reflection
center, missing row negation, changed norm coefficient and unlicensed
preliminary bound, and a wrong target guard slot. The proof is ordinary integer algebra, with finite
exact coefficient checks. No old emitter, array generator, Lean build,
internal-model transfer or frozen-file modification occurs.
