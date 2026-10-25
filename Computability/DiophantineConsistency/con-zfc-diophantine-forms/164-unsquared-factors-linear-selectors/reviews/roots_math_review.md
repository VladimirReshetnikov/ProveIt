# Independent mathematical review: Round 20 root circuit

**Verdict: PASS for the stated ordinary reduction and exact 13/152/119 metrics.**
No mathematical defect was found in the reviewed circuit, complete shear,
signed zero-existence maps, or cancellation-aware degree argument. This review
does not promote the inherited ordinary native/refutation calibration to a
newly reconstructed proof-assistant or encoded object-language certificate.

## Scope and exact objects

The immediate parent is the incoming Nearest Factorial signed circuit
`ConZFC_Nearest_Factorial_2026-10-25/signed/integer13_degree152.json`, not the
older Round 19 degree-156 family. Its SHA-256 is
`44c6c004e4252574c793ba2574540bdafb58187da96d0d7b4a9f8a6a0543869a`.

The reviewed child is `roots/integer13_degree152_ops119.json`, SHA-256
`bcb1d86b5e38d784b63b382d51054aeeaa8d65ba4ffd88b1456636ee76ec63f6`.
The reviewed proof and report section have respectively these SHA-256 values:

* `PROOF.md`: `e30386fad43f0a2b009ad20f05a8bba5b9e6b19868d4db32611df9f87784a63f`
* `report_section.tex`: `034305878300797c20f3164eeb5de74916c9bb8b93f903d454755f2cf1b247c2`

`check_roots_independent.py` was separately written for this review. It imports
neither the circuit builder nor either circuit checker. It reads the two JSON
DAGs, checks independently written free-polynomial register cuts, and covers
every node. The reviewed finite coefficient constructor is the only retained
executable imported; it constructs fixed integers from finite tables, not a
machine execution, refutation search, or Diophantine zero search. All code was
inspected before execution.

## Literal bytes, tuple, inputs and cost

All **188** retained inherited files were compared byte-for-byte with the
incoming signed packet, in addition to checking all 188 inherited pins.
This includes the parent circuit, all six coefficient payloads, coefficient
recipe, signed ordinary proofs and native/refutation calibration texts.

The six ports are exactly `beta,K0,MC,MF,cone_A,cone_B`, the coherent
`mixed-parity-unrounded-1064921` tuple. MF is `MF_native+beta`, already shifted.
All six decompressed payloads (615883 bytes total) match their raw digests,
bit lengths, and positive integer values. An independent invocation of the
inspected finite constructor rebuilt beta, K0, MC and shifted MF; the two cone
coefficients were checked against their explicit powers of two. Its finite
basis audit has 69230 convolution checks. This is not merely a generic-port
identity or a comparison of metadata names.

The literal variable list has exactly thirteen unrestricted integer inputs:
`j,C,z,h,r,v,w,T,c,n,y,p1,p2`. Both graphs use only integer, variable and fixed
coefficient leaves and binary addition, subtraction and multiplication.

| Circuit | Live nodes | Multiplications | Additions | Subtractions | Operations |
|---|---:|---:|---:|---:|---:|
| Incoming 13/152 parent | 153 | 76 | 26 | 24 | 126 |
| New 13/152 child | 146 | 71 | 24 | 24 | 119 |

All nodes, all thirteen declared inputs, and all six coefficient ports are
live. Shared `ga*fc` is one literal multiplication. Squares and scalar
multiplications are charged normally. `uu=(V+y)^2` and `u=V+y`, if used as
notation, introduce no independent input. All 119 single-gate arithmetic
corruptions were rejected **after repairing the mutated operation-count
metadata**, so these negative controls test algebra rather than stale counts.

## Whole-polynomial identity and inverse

The frontend is identical in the two graphs. In particular the incoming
`ell=XY^2`, `k=R+1+h ell`, and q-sixth-power budget are retained. The checker
verifies from graph dependencies that k is independent of n.

Write `Z=Un+MKlo+H(Y-q^3)` and
`A(z)=(z+Uk)^2+4U(Lz-U)`. Direct expansion gives

```
A(Z-Uk) = Z^2+4ULZ-4U^2(1+Lk),
A(Z-Uk)+4U^2[1+L(L+k)] = (Z+2UL)^2.
```

The independent check substitutes this identity into **both terms of the
entire norm**, not merely its leading part. It also proves

```
(V+y)^2-Q[(V+y)^2-V^2] = V^2-(Q-1)y(2V+y).
```

Consequently `P_new(n)=P_parent(n-k)` in the free polynomial ring. The inverse
is `n_new=n_parent+k`; all other inputs and all fixed coefficients are unchanged.
These integer polynomial maps are inverse on every assignment, hence restrict
to a bijection of the full integer zero sets. No sign, nonzero carrier,
canonical-witness choice, or division assumption is required for this identity.

## Signed zero-existence maps and boundary cases

The direct proof in the new proof and TeX section is also correct. Before any
zero assumption, q and H are nonzero, U is nonzero, Delta is at least 3, Dt is
positive odd, Fs is positive, and G is 1 modulo 4 and therefore nonzero.
Since N is a square modulo 4, `(N+1)Ea=1` forces N=0 and Ea=1; the unwanted
unit pair `(-1,-1)` would require N=-2 and is excluded.

The checked eight-factor identity is

```
N/U^8 = product (rho-e1 sqrt(G)-2 e2 sqrt(Dt)-4 e3 sqrt(Fs)),
rho=Zc/U, (e1,e2,e3) in {+1,-1}^3.
```

This identity holds over the complex numbers without positivity assumptions.
If G<0, it contributes the sole nonreal radical to each factor, so no factor
vanishes. G=0 is already impossible. Dt and Fs cannot be zero. At a zero all
three are therefore positive. Within each common irrational square class, a
group containing G has a unique odd coefficient; a group without G but with
Dt has a unique coefficient of exact 2-adic valuation one; the remaining
possible group contains only the nonzero Fs term. None can cancel. Thus the
shared-squareclass and even-squarefree-class cases are covered, not assumed
away by generic distinctness. All radicals are integral with the signs of the
vanishing factor. Value-one radicands cause no exception.

For these signed roots `g,tau,f`, the direct map into the changed incoming
fifteen-variable kernel is

```
f15=f, p3_15=(g-1)/2, n15=n_new-k-g-4f.
```

It gives `Z15/U+2L+k=2tau`, the first carrier residual zero, `f^2=Fs`, the
same Q and V, the same auxiliary residual, and the exact ternary guard.
Conversely, from every fifteen-variable zero, the rational centered carrier
whose square is `4Dt` is an even integer. With `g=2p3_15+1`, use

```
n_new=n15+k+g+4f15
```

and delete f15,p3_15. These maps are integral for every zero, including all
eight sign branches. No division by rho is used; its oddness and nonvanishing
are conclusions. No new simultaneous Pell existence claim is hidden here.
The fifteen-variable reduction is an existence equivalence; the thirteen to
thirteen shear is the stronger exact zero-set bijection.

## Complete leading form and exact degree 152

The raw DAG max/sum degree bound is **172**, not 152. Two cancellation cuts
must be used. They are exact and separately verified.

First, `Zc^2-db` has degree 26 after its degree-30 cancellation. Its complete
top is `-4 U0^2 ell0 k0^2`. The degree-58 inner form is
`-16 U0^4 L0^2 G0`. The entire degree-116 norm top is
`256 U0^8 L0^4 G0^2`. The complete formal weighted expansion uses weights
`(Z,U,L,k,G,Fs)=(7,6,9,5,16,12)` and yields these exact results.

The frontend leading forms were independently propagated with a check that
no unaccounted leading cancellation occurs. In particular

```
q0=6 beta j, X0=12q0 w, Y0=v,
F0=12wC-q0 z, R0=-q0^3 F0,
ell0=X0 Y0^2, k0=R0+h ell0, a0=X0Y0, U0=8q0^3 a0,
T0=cone_A^2 Y0^2 F0^2+4q0^2Y0^4+q0^6,
G0=-4k0^2T0.
```

The entire `h ell0` term is retained: it has the same degree as R0.
Substitution gives the complete norm top
`4096 U0^8 ell0^4 k0^8 T0^2`. Its subtracted correction has degree 112 and
cannot cancel the degree-116 square.

Second, `uu-V^2=2Vy+y^2` has degree 18, not 34. Ea therefore has degree 36,
with complete top `32 a0^6 r^4 c^8 R0 y`. The product of these two displayed
tops is the **entire** homogeneous degree-152 part of P. The verified actual
coefficient is

```
[j^90 w^18 v^22 z^9 r^4 c^8 y] P = 2^167 3^108 beta^90 > 0.
```

This is a nonzero coefficient for the supplied fixed beta, not just a generic
parameter. Its exponents sum to 152. Thus the upper bound is attained.

## No conflict with the older n-only obstruction

Round 19's degree-156 obstruction applies to its fixed degree-18 guard and
old first-index frontend. The incoming degree-152 parent had already changed
the first-index modulus from XY to XY^2 and the budget from q^8 to q^6.
Those are not n-only changes. The present shear preserves that incoming
degree 152 and improves its evaluator from 126 to 119 gates. It does **not**
lower the old 156-degree family by an n-only shear, disprove the scoped old
obstruction, or give a global minimality result. Against the old 13/156/117
endpoint, the new endpoint is a tradeoff of two extra gates for four degrees.

## Calibration and evidence boundary

The immediate parent's ordinary proof supplies its signed-index changes,
soundness into the earlier B0-only calibrated predecessor, and canonical
completeness construction. The retained ordinary native/compiler/refutation
theorem supplies the final Con(ZFC) calibration. The new exact bijection
transports that theorem without changing the tuple or native encoding.

The preserved `CALIBRATION_STATUS.md` and `FORMALIZATION_BOUNDARY.md`
correctly distinguish this referenced ordinary proof from the separate,
still absent end-to-end encoded object-language/native proof artifact. This
review checked that dependency and its retained bytes, not every predecessor
theorem from first principles. No finite test, external Lean source, or
polynomial identity is represented as closing that separate formalization
obligation.

Replays passed normally and with Python optimization enabled:

```
python3 -B round20/review/check_roots_independent.py
python3 -B -O round20/review/check_roots_independent.py
```

Receipts: `roots_independent_normal.json` and
`roots_independent_optimized.json`; corresponding logs are retained. Their
checker hash and reviewed JSON hash bind this result. The remaining boundary
is inherited ordinary calibration, not a newly discovered algebraic defect.
