# Next adaptive checkpoint: positive main carrier and index congruence

This is a read-only proposal for `NativeAdaptiveMainBootstrap.lean` and
its focused Checks. No new Lean source, compiler run, historical generator,
equation, metric, or consistency endpoint is supplied here. The accepted
first-carrier and independently replayed factor-three packets provide the
two prerequisites. All existing frozen files remain unchanged.

The smallest useful next endpoint is: the literal A1 equation, positive
inputs, first-carrier divisibility, and the elementary inequality v<k
give a **positive integral main Pell root** and **q^4 dividing v**. The
rank upper bound, first-index lower bound, large-c bounds, and restored
source are not needed for this endpoint.

## Literal cuts and domain

I rechecked rows 1–65 of the actual 88-row
`candidates/free-j-polarized-positive/source/positive/p13_free_J.json`
against its ordinary proof. The full positive input order remains

```
J,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma.
```

In this checkpoint all displayed cuts are integers. The relevant ones are

```
q = beta*J+1                  k = eta+zeta
C = q-F-alpha                c = k*Y+eta
a = Y*(X+1)                  H = 4*a+3
Delta = (a+2)^2-1             U = q^2*Y
R = ((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
v = k-R-1
Dstar = U*(X+a*c)+H*(U*gamma+q*X*Y-v)
A1 = Dstar^2-U^2*(1+Delta*c^2).
```

These are rows 5, 9–19 and 43–65, with `a=E+Y` and
`Delta=a^2+H` expanded by ring identities. The graph's `qF` means q−F,
and its `r0` is signed v, not the positive input r. In particular no
positivity of v, Dstar, or a quotient is assumed from the input domain.
There is no J congruence restriction and no coprimality-with-three premise.

The current interpretation of the ports is the same complete 47313-byte
tuple as in the accepted first proposal: beta, K, lowPort, highPort+beta.
MF is already shifted exactly once. This generic packet need not import
those concrete constants, re-evaluate them, or claim their historical
13/88/51 evaluator has already been transferred.

## Derive the structural inequality before touching A1

Define a generic signed target polynomial

```lean
def target (q F alpha J MC MF : ℤ) : ℤ :=
  ((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J

theorem target_positive {q F alpha J MC MF : ℤ}
    (hq : 1 < q) (halpha : 0 < alpha) (hJ : 0 < J)
    (hMC : 0 ≤ MC) (hMF : 0 ≤ MF)
    (hC : 0 < q-F-alpha) :
    0 < target q F alpha J MC MF
```

Indeed q−F=C+alpha>0, so the first parenthesis is positive, q²−1>0,
and the second summand is nonnegative. Thus the literal
`v=k-target q F alpha J MC MF-1` satisfies v<k. This uses neither the
upper port box nor an R window, a source rank, a Pell index, or a bound
on F supplied independently of C.

For actual positive inputs the accepted
`NativeAdaptiveCarrierBootstrap.first_carrier_integral_positive`
supplies q³|Y and Bt>0; its `transport_positive` supplies C>0.
q>1 follows from beta>0 and J>0. The already accepted current interface
provides beta≥15, K≥0, and nonnegative MC/MF. Hence no desired conclusion
is hidden in the generic v<k hypothesis. A small literal target client can
eliminate that hypothesis using `target_positive` in the same new file.
The upstream extraction of A0=A1=0 from the complete thirteen-input
product is still a separate literal-evaluator obligation.

## Positive Dstar without a window or index

Assume q>1, X,Y,k,eta,gamma>0, q³|Y, and v<k. Since the values are
integers, q≥2. Write Y=q³s. Positivity gives s≥1, hence Y≥q³≥8.
In particular Y≥2, a=Y(X+1)≥4, and U>0. Put

```
B = U*a*Y-H = a*(q^2*Y^2-4)-3.
```

Already q≥2 and Y≥2 imply q²Y²≥16, so B≥12a−3>0. The exact identity

```
Dstar-k*B
  = U*X+U*a*eta+H*(U*gamma+q*X*Y+k-v)
```

has positive right side. Thus Dstar>kB>0. This deliberately derives the
actual signed root's positivity; replacing it by |Dstar| would lose the
transport equation needed next. The argument requires no size or sign
information about v other than v<k.

Suggested literal definitions, using local cuts to avoid ambiguity:

```lean
def mainDstar (q X Y k eta gamma v : ℤ) : ℤ :=
  let a := Y*(X+1)
  let c := k*Y+eta
  let H := 4*a+3
  let U := q^2*Y
  U*(X+a*c)+H*(U*gamma+q*X*Y-v)

def mainA1 (q X Y k eta gamma v : ℤ) : ℤ :=
  mainDstar q X Y k eta gamma v ^ 2 -
    (q^2*Y)^2 * (1+((Y*(X+1)+2)^2-1)*(k*Y+eta)^2)

theorem mainDstar_positive {q X Y k eta gamma v : ℤ}
    (hq : 1 < q) (hX : 0 < X) (hY : 0 < Y)
    (hk : 0 < k) (heta : 0 < eta) (hgamma : 0 < gamma)
    (hYdiv : q^3 ∣ Y) (hv : v < k) :
    0 < mainDstar q X Y k eta gamma v
```

## Integral positive main norm and the exact factor-three transport

From A1=0 obtain Dstar²=U²(1+Delta*c²). Thus U² divides Dstar²;
`Int.pow_dvd_pow_iff two_ne_zero` gives U|Dstar. Choose the signed integer
D with Dstar=U*D. Since U and Dstar have just been proved positive, D>0.
Cancel U² to obtain

```
D^2 = 1+Delta*c^2.
```

The definition of Dstar and the actual equality Dstar=UD give the exact
ring identity

```
H*(q*X*Y-v) = U*(D-X-a*c-H*gamma).
```

It follows that U divides the left side. From Y=q³s we have U=q⁵s,
so q⁵ divides H(qXY−v). Apply the accepted signed theorem

```lean
NativeAdaptiveFactorThree.index_difference_dvd
  (hY : q^3 ∣ Y)
  (hd : q^5 ∣ (4*Y*(X+1)+3)*(q*X*Y-v)) : q^4 ∣ v
```

without adding `gcd(q,H)=1`, q modulo 3, or positivity of v. That theorem
handles q divisible by three with the precise loss of at most one q.
No division by an unproved unit occurs.

Finally a>0 and c>0 allow natural casts. Use the expanded polynomial
`Delta=a^2+4*a+3` when transporting the norm, then identify it with the
natural `(a.toNat+2)^2-1`. The generic accepted theorem is exactly

```lean
NativePellBootstrap.main_classification {a c D : ℕ}
  (hc : 0 < c)
  (hnorm : D^2 = 1+((a+2)^2-1)*c^2) :
  ∃ p, 0 < p ∧ D = Pell.xn (by omega : 1 < a+2) p ∧
    c = Pell.yn (by omega : 1 < a+2) p
```

Its generic version, not any `source_*` theorem, supplies the main index.

The proposed public bundle is therefore:

```lean
theorem main_carrier_bootstrap {q X Y k eta gamma v : ℤ}
    (hq : 1 < q) (hX : 0 < X) (hY : 0 < Y)
    (hk : 0 < k) (heta : 0 < eta) (hgamma : 0 < gamma)
    (hYdiv : q^3 ∣ Y) (hv : v < k)
    (h1 : mainA1 q X Y k eta gamma v = 0) :
    let a := Y*(X+1)
    let c := k*Y+eta
    ∃ D : ℤ, 0 < D ∧
      mainDstar q X Y k eta gamma v = q^2*Y*D ∧
      D^2 = 1+((a+2)^2-1)*c^2 ∧
      q^4 ∣ v ∧
      ∃ p : ℕ, 0 < p ∧
        D = (Pell.xn (by omega : 1 < a.toNat+2) p : ℤ) ∧
        c = (Pell.yn (by omega : 1 < a.toNat+2) p : ℤ)
```

A final wrapper can use the identical conclusion with
`v=k-target q F alpha J MC MF-1`, replacing hv by the explicit positive
target hypotheses. This is an all-positive soundness deduction from the
two displayed carrier equations. It is not canonical completeness and
does not assume the source that it is intended eventually to reconstruct.

## Freeze boundary and focused controls

Stop at this bundle and the target client. Defer all of the following:
R<q⁴, comparison of first and main indices, p≥6, c>A*Delta², c>2R,
p=R, strong/auxiliary reconstruction, X=2^R, the positive gamma lift in
the converse, and any full historical polynomial/current-source endpoint.
The accepted ordinary and shifted-source existence adapters remain
downstream consumers, never bootstrap premises.

Focused checks should exercise the generic bundled theorem, the target
client without any J residue premise, Dstar positivity with q=3 and a
negative v, and positive-root casting at a small main Pell solution.
Such numerical controls are scoped arithmetic examples, not asserted
full thirteen-variable zeros. Print axioms for the actual public
endpoints. No `native_decide`, new axiom, source assumption, or semantic
oracle is needed.

## Import/cache feasibility and source pins

Proposed imports are only

```
DiophantineConsistency.NativeAdaptiveCarrierBootstrap
DiophantineConsistency.NativeAdaptiveFactorThree
```

Their union is the same authenticated 25-module NativePellBootstrap
closure plus these two frozen leaves: **27 reused custom modules**, the
same **22 actual external names including Init**, and **66 external
artifact companions**. There is no Foundation module, new external
boundary, or prerequisite build. A future execution would build only the
new main and Checks in a fresh private overlay, retaining -M6000, -j1,
async=false, regular nonsymlink target outputs, and the 512 MiB reserve.
Every selected source/object and actual boundary must again be rehashed
before and after; this proposal does not authorize execution.

The base inventory is
`adaptive-carrier-bootstrap2011-cache-audit.json`, SHA256
`21917ee6855045afd5c9494868c431f2bd8e2ed67b3ef621e8772f42cdc6b915`.
The two additional current pairs are:

| Module | Source SHA256 | Object SHA256 and provider |
|---|---|---|
| NativeAdaptiveCarrierBootstrap | `0975b336fd452dff7c68a8ccb795c8af516c2c08dac6940542b0f148f2dc1761` | `2ef643d6db2ac5d0b0b7911416e260e9469aa6cd7076899a2b93309dfa722f6a`, `/tmp/native-adaptive-bootstrap-root-qdo6f38v/lib` |
| NativeAdaptiveFactorThree | `cf7ebc1c3af93eb4ca800f309c411445dd267d0bf7d3bda437620be6cc702a67` | `bcb54d6683b952870f88545ea5a85bfcb67ef335f89f30f45044385c6b18c4a8`, `/tmp/native-adaptive-factor-three-peer-0z7ha_1s/lib` |

The root first-carrier replay ROOT hash is
`701b30dcd0a0dcc91f1fe57e5d0d8c8b6a1696d4eac8db143daa10e0acaf4204`.
The complete factor-three independent replay hash is
`cf5f3beb416e1829623e25765f69166c9399ab64aa655c812f59ae3f9710ac30`;
its peer receipt is
`a2a9b880c4d1550520402b72b412b4038c39bbc3f5c5ba0e0a6b04d82defa4e8`.

Other exact read dependencies:

| File | SHA256 |
|---|---|
| Actual `p13_free_J.json` | `a6c378ffe706da6ccb17250c31183b0cbff7bdd2c21b85cf0fc393a73bd987b8` |
| Its ordinary `PROOF.md` | `4ce1e588973c7f703dea6a3c60ce747f6f0416544a522fe408d7d81a78a08dcf` |
| NativePellBootstrap.lean | `351d51db7e438b4c9bb8f80f4146df1e9516704c4e47719e562fb9ce9ed521e4` |
| Frozen first proposal | `cdddfed4a9436479554f6f34808498fb090e11d141f1060e3869c6e2243b5af4` |

The controller agent independently challenged only the displayed Dstar
identity, its positivity estimate, integer square cancellation, and the
factor-three reduction; it found no issue. That limited mathematical
challenge is not a full source review, Lean replay, or equation-transfer
certificate. This note itself makes no new equation-size or HA/ZFC claim.
