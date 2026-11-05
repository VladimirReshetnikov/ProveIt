# Independent review of alternate-witness rigidity

**PASS in the stated source and standard-integer scope.** The reviewed
[analysis](../../research/p64-qcube72-alternate-witness-rigidity/README.md)
gives necessary restrictions on possible witness changes; it does not prove a
76Y witness exists, exclude a different witness, or establish a standalone
Lean theorem for the 72-to-76Y direction. Its fixed-port application remains
conditional on an actual positive 72 zero and the stated carrier-gap
assumptions. The earlier captured-provider, object ancestry, and external
file-binding qualifications remain in force.

For fixed positive `X,Y,k,c`, put `U=Y²`, `a=(X+1)Y`, and `H=4a+3`.
If two **positive** roots of the same square have the forms
`U(X+a*c)+H*h₁` and `U(X+a*c)+H*h₂`, they are equal. Since `H>0`,
`h₁=h₂`. Also `eta=c-kY` and `zeta=k-eta` are fixed. This is ordinary
integer algebra, independent of Pell classification. The old 76Y expression
can involve the signed difference `U*gamma-k+R+1`; it is essential to use
the positive oriented root supplied by the old-side argument before applying
square rigidity. For example, with `X=Y=1,c=5`, the two signed values `h=0`
and `h=-2` give opposite roots `11` and `-11` with equal squares. They do
not satisfy the positive-root premise simultaneously.

The inspected source composition updates coordinate 12 in the 76Y-to-77
witness map; the 77/78 and 78/79 comparisons use the same valuation; the
79-to-80 and 80-to-81 lifts update coordinate 9; and the q-cube lift to P64
updates coordinate 7. In particular, coordinates 0 and 8 are preserved,
so the P64 values `q=beta*J+1` and `X=w*q` match those of the 76Y witness.
The [P64 facts source](../../Lean/DiophantineConsistency/Compact44/P64Facts.lean)
uses the fixed compact beta and low/high mask assumptions, positivity, graph
zero and resulting transport, q-cube, norm, and index facts before invoking
`P72Power.power_of_mod`; it derives `X=Exp.exp R`. In ordinary integers this
is `X=2^R`, so `q | X` implies `q` is a positive power of two. The reviewed
paragraph is an inspection of that source path and its existing witnessed
maps, not a new Lean check or a fresh source-to-object ancestry audit.

For `B>0`, `(2^B-1) | (2^d-1)` exactly when `B | d`: write `d=Bt+r`
with `0≤r<B` and reduce modulo `2^B-1`. If the remainder
`2^r-1` vanishes, its size forces `r=0`. Thus for positive `J,d`,
`(2^B-1)J+1=2^d` exactly when `d=Bt` for positive `t`, and then
`J=sum(2^(Bj), j=0..t-1)`. A power of two is not divisible by three.
This restricts a conversion that preserves `q`; it does not exclude a
conversion that changes `J`, `q`, or the other coordinates. In particular,
changing `F` or `alpha` can change `R`, so fixed-scale root rigidity is not
an existence-level impossibility result.

The independent [checker](check.py) pins the source fragments reviewed above,
reproduces the author's finite controls, tests 124,148 positive-root square
comparisons (allowing signed `h` when the root stays positive), includes the
opposite-root negative control, and independently tests 3,456 bounded
repunit cases. These are finite controls and source checks, not proofs of the
general statements or a Lean replay. Run:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-alternate-witness-rigidity-independent/check.py
```
