# Adaptive power recovery after the literal strong index

Read-only proposal; no new Lean source, compiler invocation, historical
generator, or candidate evaluator. This advances soundness for the complete
unrestricted-J thirteen-positive graph. Canonical completeness and restoration
of all source rows remain separate. The proposed first packet is
`NativeAdaptivePowerRecovery` plus focused checks, importing only the frozen
`NativeAdaptiveStrongIndex`. A subsequent small Mersenne packet can exclude the
exceptional factor three and recover the binary cell base.

## Literal inputs and the correct first index

Retain all thirteen positive integer inputs
`J,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma` of the complete historical
`source/positive/p13_free_J.json`. Its formulas are:

```
k=eta+zeta, c=kY+eta, a=Y(X+1), A=a+2, H=4a+3,
Q=XY^2, P=2Q+1, U=q^2Y, v=k-R-1, q=beta*J+1,
Bt=(q*K+X)*(q-F-alpha)-q*F,
R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
Dstar=U*(X+a*c)+H*(U*gamma+q*X*Y-v).
```

Here MF is already shifted exactly once; the target is the exact existing
`NativeAdaptiveMainBootstrap.target`. The positive input r belongs to A0;
below `r0=n-1` is a newly derived Pell index, not that input. The public
premises remain `PortBox ports`, `15<=ports 0`, all input positivity, the
literal definitions, A0=A1=0 and Fs=Fa=1. In particular add the actual
`k=eta+zeta`, `zeta>0` relation to the Strong wrapper, which previously needed
only k>0. It is essential to the upper ratio bound and must not be omitted.

The correct first-index identity is **2n=R+1**, not n=R. No classification,
index, rank parity, q|X, power, coprimality, or restored-source premise is added.

1. Call `adaptive_early_bounds`: it supplies n>=25, n<p, the first ordinate
   k=2*yn_P(n), the main ordinate c=yn_A(p), and R+1<q^4. Call
   `adaptive_main_index_exact`: the same actual c is yn_A(R.toNat).
   `Pell.strictMono_y` gives p=R.toNat. Because R>3q>=48, all conversions
   `(R.toNat:Int)=R` are valid, and n<R in integers.
2. A0 supplies Y=q^3*s with s>0. A1 supplies q^4|v even if 3|q. The cached
   `first_index_residue_of_dvd` gives q^4|(2n-R-1), since q^4|2Q. Its
   companion lower lemma already gives R+1<=2n. Thus
   `0 <= 2n-R-1 < R-1 < q^4`; integer divisibility forces this difference
   to zero. This does not assume that 2n itself is below q^4.
3. Put r0=n-1. Then r0>=24 and R.toNat=2*r0+1, deriving oddness. The exact
   first Pell congruence modulo P-1=2Q, doubled, yields **4Q|v**. Therefore
   **U|v**, using `4Q=U*(4Xq*s)` and Y=q^3*s. If useful, v>0 follows from
   `Diophantine.lt_yn_of_two_le` and n>=25, but no positive quotient is
   needed for the projection proof.

The existing `NativePellFirstIndex.first_index_exact` is a useful proof
reference, but accepts a nonnegative natural quotient in
`k=1+R+E*h`. Supplying that equation prematurely would be circular. The
signed divisibility helpers already imported through RankWindow avoid this.

## Projection without gcd or an exceptional-case hypothesis

Write v=U*t with t an integer. The classified positive main root has
Dstar=UD. Define L=D-X-ac and B=q*(gamma-t)+X. Cancelling the positive factor
qY in the literal Dstar identity gives

```
q*L=H*B.
```

Because Y=q^3*s, set h0=4q^2*s*(X+1); then H=q*h0+3. Consequently

```
3*L = H*(L-h0*B),
3*X = q*(L-H*(gamma-t)-h0*X).
```

Both are finite ring identities after qL=HB. They establish **H|3L** and
**q|3X**, uniformly including 3|q. There is no cancellation of H from a
divisibility, no assertion that q and H are coprime, and no division by a gcd.

The already cached `Diophantine.χ_modEq_pow` with base A=a+2 and argument
2 gives `H | D-ac-2^R`. Convert its natural modulus to the positive integer
H, using the exact main classification at R.toNat and positive a. Combining
with H|3L yields

```
H | 3*(X-(2:Int)^R.toNat).
```

There is no separate `NativePellProjection.lean` in the current tree. The
needed generic projection is `Common/Pell.lean:97`, and its modulus is
exactly `2*(a+2)*2-2*2-1=4a+3`.

## Growth that is valid before q divides X

Use natural representatives only after recording positivity and cast
equalities for X,Y,k,c,a,R. The cached generic Pell bounds give

```
(2A-1)^(2r0) <= c,
k <= 2*(2P)^r0.
```

The exact positive cross-product identity is

```
X*(2A-1)^2-2P*(X+1)^2
  = 12XY(X+1)+9X-2(X+1)^2 > 0.
```

For X,Y>=1 its right side is at least 10X^2+17X-2>0. Raising the strict
cross-product inequality to r0>0 and using the two Pell bounds gives

```
k*(X+1)^(2r0) < 2*c*X^r0.
```

The **actual** eta/zeta split gives c=kY+eta<k(Y+1). Cancelling positive
k and X^r0 as appropriate yields the retained sharp inequality

```
(X+1)^(2r0) < 2*(Y+1)*X^r0.                     (G)
```

This is the integer proof behind `Ratio90.lower_estimate` and
`NativePellPower.doubled_ratio_lower`. It can be proved directly from cached
`Diophantine.pow_le_ψ_succ` / `ψ_succ_le_pow`, using the short cross-product
argument, without importing the real-ratio module or its source clients.
Only the integer portion of Ratio90 was inspected for this reuse; no claim
of a new review of its later real-analysis proofs is made here.

For X>=2, the identity
`2*(X+1)^2-9X=(2X-1)*(X-2)>=0` and (G) imply
`9^r0 < 2^(r0+1)*(Y+1)`. The finite integer inequality
`9^16>6*8^16` extends to every r0>=16 by multiplication and 9^j>=8^j.
Also `2^(r0+1)*(2^(2r0+1)+1)<=6*8^r0` for r0>=0. If Y<=2^R,
these inequalities contradict one another. Thus **2^R<Y**.

Both X and 2^R now lie in (0,a): a=Y(X+1), Y>=1, and X>0.
Therefore `|3*(X-2^R)|<3a<H`. The signed divisibility proved above forces
X=2^R, without any Mersenne hypothesis yet.

For X=1, (G) gives `2^(2r0)<2*(Y+1)`. Since r0>=24, dividing the even
left side by 2 and using integrality gives `2^(2r0-1)<=Y`, hence
**2^R<=4Y**. Now H=8Y+3, R>=49, and

```
0 < 3*(2^R-1) < 2H.
```

The positive multiple of H must be exactly H. Thus
`8Y=3*2^R-6`. Since R>=3, 8 divides 2^R; reduction modulo 8 is impossible.
This excludes X=1. Rank oddness is derived, but the contradiction needs only
the already-derived R>=3. No excluded X=1 assumption is smuggled into (G).

`NativePellPower.two_pow_rank_lt_Y` requires X>=16. Its source-based proof
gets that from X=q*w, precisely a deleted source row. It cannot be invoked
here before recovering q|X. The stronger integer (G) is the missing bridge.

## Proposed first public interface

These are proposed declarations, not yet Lean-checked signatures. With the
same named cuts as the frozen modules, the wrapper should have exactly:

```
adaptive_X_eq_two_pow (ports : Fin 4 -> Int)
  (hports : PortBox ports) (hbeta : 15 <= ports 0)
  {J F alpha X Y k eta zeta gamma r q R Bt f i T u : Int}
  (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha)
  (hX : 0<X) (hY : 0<Y) (heta : 0<eta) (hzeta : 0<zeta)
  (hgamma : 0<gamma) (hr : 0<r)
  (hf : 0<f) (hi : 0<i) (hT : 0<T) (hu : 0<u)
  (hk : k=eta+zeta)
  (hq : q=ports 0*J+1)
  (hR : R=target q F alpha J (ports 2) (ports 3))
  (hBt : Bt=(q*ports 1+X)*(q-F-alpha)-q*F)
  (h0 : firstA0 q (X*k*Y^2) k r Y Bt=0)
  (h1 : mainA1 q X Y k eta gamma (k-R-1)=0)
  (hs : strongFactor (Y*(X+1)) (k*Y+eta) f i=1)
  (ha : auxiliaryFactor (Y*(X+1)) (k*Y+eta) f T R u=1) :
  X=(2:Int)^R.toNat and q | 3*X and
  exists n:Nat, 25<=n and 2*(n:Int)=R+1 and
    k=2*(Pell.yn (by positivity : 1<2*(X*Y^2).toNat+1) n:Int) and
    4*X*Y^2 | k-R-1 and q^2*Y | k-R-1
```

The proof-argument placeholder in that displayed Pell type means an explicit
proof after positive Q and its toNat cast have been established. No desired
index equality is a public premise. A useful modular decomposition is:

* signed exact first-index helper, plus a literal classified-data wrapper;
* U-divisibility and the two explicit projection witnesses;
* doubled ratio and the two small integer growth lemmas;
* signed small-multiple uniqueness, X=1 exclusion, and the public wrapper.

Focused checks should retain a generic q divisible by 3 in the projection
identity, exercise the X=1 contradiction, and expose the wrapper without
source, oddness, index, X>=2, or power assumptions. These are theorem tests,
not a decision procedure enumerating large Pell witnesses.

## Separate Mersenne stage: exact factor-three exclusion

This is a concrete follow-up, not needed to prove X=2^R. Let d>=4 and
beta=2^d-1. Assume q>1, beta|(q-1), and q|3*2^R, as already derived for
the literal tuple. If 3|q, write q=3m with m>0; cancel literal 3 to get
m|2^R. `Nat.dvd_prime_pow Nat.prime_two` gives m=2^u. It remains to prove

```
mersenne_not_three_power (d u : Nat) (hd : 4<=d) :
  not ((2:Int)^d-1 | 3*(2:Int)^u-1).
```

Write u=d*j+r, r<d. Since 2^d is 1 modulo beta, 3*2^u is congruent to
3*2^r. For r<=d-2, its value is at least 3 and at most
3*2^(d-2)<2^d-1. For r=d-1, its remainder is 2^(d-1)+1, strictly
between 1 and beta. Neither is 1. This proof needs d>=4, but no parity of
d, no numerical expansion of beta, and no multiplicative-order oracle.

Thus 3 does not divide q. `NativeAdaptiveFactorThree.bezout_three` then
cancels 3 from q|3X, giving q|X. Apply prime-power divisor classification
again to obtain q=2^u with 0<u<=R. A later width helper proves d|u from
beta|(2^u-1); `NativeBinaryScale.width_dvd_exponent` is the exact existing
generic contract. It can be reused later, or its elementary modular proof
repeated in the small Mersenne leaf to avoid importing source clients.

The actual current data give `width=47*2011=94517`,
`beta=(2^47)^2011-1=2^94517-1`. The four ports are exactly
`[beta,K,lowPort,highPort+beta]`. Consequently d>=4 and the needed width
identity hold for the current 47313-byte tuple, just as for the different
historical compact44 tuple. The latter's numerical coefficient bytes and
historical calibration are not reused as current premises. An actual-port
wrapper can be deferred to the final graph/source adapter: the first
generic power leaf needs no current finite table imports or new port proof.

This does not yet restore gamma_old, the positive source coordinates,
canonical completeness, the 12-variable elimination, or any HA endpoint.
No historical 88/51 metric is newly certified by these arithmetic lemmas.

## Pins and minimal cache delta

The companion `adaptive-power-recovery2011-cache-audit.json` records every
source/object pair and boundary pin inspected for this plan. It extends the
Strong author's final authenticated closure by only that newly compiled
main: **30 cached custom modules, 22 actual external names (including
Init), 66 external object companions**. All selected bytes were rehashed.
No prerequisite build or new external import is proposed. The compiler is
the pinned Lean 4.32.0 binary. No cache files were copied or mutated.
The audit SHA-256 is
`a5d0e78f9676f0686803108048f991b2e2b3d1826ca5031066c1a58cc2ad6fac`;
155 inherited/new pin observations passed, with 2,181,201,920 free bytes.

Key source pins (the JSON contains the complete reference inventory):

| Source | SHA-256 |
| --- | --- |
| `NativeAdaptiveStrongIndex.lean` | `6e0e0a65b62defe5759f54eeb9a527a48a5d7d8ffb35021187930acb44098284` |
| `NativeAdaptiveRankWindow.lean` | `f536f9324408a9660967e62baf10f01d85ed45ef7e4619e1c9f32710c6bd9b52` |
| `Common/Pell.lean` | `e5fdac7c9062eb7cbdaa5d649290fbac16c2415f1fbaf0ab3415454b55ec3560` |
| Complete `p13_free_J.json` | `a6c378ffe706da6ccb17250c31183b0cbff7bdd2c21b85cf0fc393a73bd987b8` |
| Free-J ordinary `PROOF.md` | `4ce1e588973c7f703dea6a3c60ce747f6f0416544a522fe408d7d81a78a08dcf` |

The new provider is `/tmp/native-adaptive-strong-eknra1gh/lib`; its source
and object hashes are recorded along with the full durable author packet.
Root reports a fresh independent main/check replay, byte-identical, with
6.705/2.855-second timings and three standard axiom reports. This audit is
read-only and does not relabel that author/root evidence as our new replay.
The preceding RankWindow provider remains recorded at its original path;
root's accepted replay is byte-identical, so no path substitution is hidden.

`NativePellPower`, `NativePellFirstIndex`, `NativeBinaryScale`, Ratio90 and
the historical graph are pinned reference sources, not newly selected
objects. The proposed integer proof uses already cached `Common.Pell` and
`PellMatiyasevic`; the latter publicly imports `Mathlib.Data.Nat.Prime.Basic`
for the optional later prime-power classification. No real-ratio proof or
Foundation closure is added. Before any eventual compilation, revalidate
all selected source/object and external pins again, read the complete new
main/check/driver, keep `-M6000 -j1 -DElab.async=false`, regular private
outputs and the 512 MiB reserve, and preserve every failed attempt. This
proposal itself authorizes no execution.
