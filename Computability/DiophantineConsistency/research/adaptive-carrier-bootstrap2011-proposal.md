# First adaptive-carrier checkpoint for the current ports

This is a read-only proposal, not a new Lean theorem or a transferred
13/88/51 endpoint. No compiler, historical builder, generator, or incoming
program was executed. The suggested first leaf is
`NativeAdaptiveCarrierBootstrap.lean` with focused checks. It proves the
signed first-carrier arithmetic below before any source restoration.

## Exact historical object and current specialization

I read the entire 88-row `source` array in
`candidates/free-j-polarized-positive/source/positive/p13_free_J.json`, its
complete `PROOF.md`, and the ordinary-parent carrier arguments. Its inputs,
in their actual order, are

```
J,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma > 0.
```

There is no `J=3j+1` restriction. Its four symbolic ports are
`beta,K0,MC,MF`, where `MF` is already the source-shifted high port. At the
current specialization these mean exactly

```
CurrentWindowCarry2011.ports =
  [CurrentMasks2011.beta, CurrentKernel2011.K,
   CurrentMasks2011.lowPort,
   CurrentMasks2011.highPort + CurrentMasks2011.beta].
beta = 2^94517 - 1; 94517 = 47*2011.
```

The current definitions are in `CurrentKernelData2011` and
`CurrentMaskData2011`. This is the complete current 47313-byte tuple, not
the historical compact44 tuple used by the ordinary proof. No second MF
shift is made. The graph's arithmetic formulas do not contain the old
width or a congruence restriction on J. This observation does not by
itself prove its current-port existence equivalence or re-audit its metric.

The literal cuts, with row numbers in that 88-row array, are:

```
 1– 7: q=beta*J+1, U=q^2*Y, C=q-F-alpha
 8–20: E=X*Y, k=eta+zeta, c=k*Y+eta,
       a=E+Y, H=4*a+3, Delta=a^2+H, ell=E*k*Y
21–28: W=(q-1)*k+1, M=q^3*(q-1), Bt=(q*K0+X)*C-q*F
29–42: Z=M*(ell+k+r)+(q-1)*Y-q^3*W*Bt,
       A0=Z^2-M^2*(ell*(ell+k)+1)
43–65: R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
       v=k-R-1, Dstar=U*(X+a*c)+H*(U*gamma+q*E-v),
       A1=Dstar^2-U^2*(1+Delta*c^2)
66–82: Q=Delta*(f^2-1), I=i*c^2, Fs=1+I^2-Q,
       V=f^2*(c*T-R)-c, y=V+u, Fa=Q*V^2+(1-Q)*y^2
83–88: P13=(1+A0)*(1+A1)*Fa*Fs-1.
```

`qF` in the actual array means **q minus F**; `r0` means the signed v,
not the positive input r. Z, Bt, C, v, V and y are initially integers of
unknown sign. In particular, positivity of the thirteen inputs does not
license taking `Z/M` as a positive Pell coordinate.

Upstream unit extraction is elementary and independent of calibration:
M is even; Delta is 0 or 3 modulo 4; `1+Delta*c^2` is 0 or 1 modulo 4;
Q is 0 or 1 modulo 4. Thus none of the four factors can be -1, and an
integer product equal to 1 forces all four to equal 1. This gives A0=A1=0,
I^2=Q and Fa=1 on every integer assignment to these cuts. A future literal
13 evaluator must bind that extraction to all its rows; the first proposed
leaf below takes the actual displayed A0=0, not a claimed source witness.

## Recommended first leaf: signed A0 arithmetic only

Proposed definitions and main signature, with all variables in Z:

```lean
def firstZ (q ell k r Y Bt : ℤ) : ℤ :=
  (q^3*(q-1))*(ell+k+r) + (q-1)*Y -
    q^3*((q-1)*k+1)*Bt

def firstA0 (q ell k r Y Bt : ℤ) : ℤ :=
  firstZ q ell k r Y Bt ^ 2 -
    (q^3*(q-1))^2 * (ell*(ell+k)+1)

theorem first_carrier_integral_positive
    {q ell k r Y Bt : ℤ}
    (hq : 1 < q) (hell : 0 < ell) (hk : 0 < k)
    (hr : 0 < r) (hY : 0 < Y)
    (h0 : firstA0 q ell k r Y Bt = 0) :
    ∃ s b tau : ℤ,
      0 < s ∧ 0 < b ∧
      Y = q^3*s ∧ Bt = (q-1)*b ∧
      firstZ q ell k r Y Bt = (q^3*(q-1))*tau ∧
      tau^2 = ell*(ell+k)+1 ∧
      tau = ell+k+r+s-((q-1)*k+1)*b ∧
      0 < |tau| ∧ |tau| < ell+k
```

This signature uses no masks, A1, f, i, T, gamma, source equations, native
rank, or Pell index assumptions. The proof is finite algebra and integer
order/divisibility:

1. A0=0 implies M^2 divides Z^2. The existing
   `Int.pow_dvd_pow_iff two_ne_zero` yields M divides Z, hence Z=M*tau.
   M>0 follows from q>1. This lemma is already used in imported Mathlib
   `NumberTheory/Pell.lean`; no new number-theory import is needed.
2. Reducing Z=M*tau gives `q^3 | (q-1)*Y`. Cancellation can use the
   explicit identity `q^3-(q-1)*(q^2+q+1)=1`, so q^3 divides Y.
   Similarly `(q-1) | q^3*W*Bt`, and
   `q^3*W-1=(q-1)*(q^2+q+1+q^3*k)` gives `(q-1) | Bt`.
   Neither step needs coprimality with 3 or a new gcd lemma.
3. Choose signed s,b with Y=q^3*s and Bt=(q-1)*b. Positivity of Y and
   q^3 gives s>0. Cancel M and M^2 to obtain the two displayed tau equations.
4. Since ell,k are positive integers,
   `(ell+k)^2-[ell*(ell+k)+1]=ell*k+k^2-1>0`.
   Thus `0<|tau|<ell+k`. If b<=0 then W>0 and
   `tau=ell+k+r+s-W*b>ell+k`, a contradiction. Hence b>0 and Bt>0.

A small literal transport corollary should retain the actual sign:

```lean
theorem transport_positive {q K X F alpha Bt : ℤ}
    (hq : 0 < q) (hK : 0 ≤ K) (hX : 0 < X) (hF : 0 < F)
    (hBt : Bt = (q*K+X)*(q-F-alpha)-q*F)
    (hpos : 0 < Bt) : 0 < q-F-alpha
```

The positive coefficient q*K+X and positive q*F prove this directly.
For the literal input tuple, beta>0 and J>0 give q>1, while X,Y,eta,zeta,r
give ell>0 and k>0. All current coefficient requirements are already supplied
by `CurrentWindowCarry2011.interface.beta_ge_fifteen` and `.K_nonneg`.
The generic first leaf need not import that current-port theorem.

The useful final theorem in this first packet is signed Pell classification:

```lean
theorem classify_signed_first_norm {Q k tau : ℤ}
    (hQ : 0 < Q) (hk : 0 < k)
    (hnorm : tau^2 = 1 + Q*(Q+1)*k^2) :
    ∃ n : ℕ, 0 < n ∧
      |tau| = (Pell.xn (by omega : 1 < 2*Q.toNat+1) n : ℤ) ∧
      k = 2*(Pell.yn (by omega : 1 < 2*Q.toNat+1) n : ℤ)
```

This is a Nat-cast/natAbs wrapper around
`NativePellBootstrap.first_norm_classification`, whose premises are exactly
Q>0, k>0 and the natural norm equality. Take Q=X*Y^2 after using
`ell=X*k*Y^2`. Its positivity is established from the actual positive
inputs. Neither the sign of tau nor an integer quotient chosen nonnegative
is assumed. This is the suggested stopping point before freezing/review.

## Next main-Pell stage: precise dependencies, not first-leaf premises

After the first leaf, a second packet can use A1=0 as follows.

* C>0 and `NativePellBootstrap.PortBox` for the actual four ports give
  `3*q<R<q^4-2`, with q>=16. No source rank is introduced. The stronger
  upper-bound identity already displayed inside `source_window_bound`
  can be reproved for the literal target polynomial R:
  `q^4-q^3-q-1-R = q*(q^2-1)*(F-1)+(q^2-1)*(C-1)+(q+1)*(J-1)
    +J*((beta-MC-1)+q*(2*beta-MF-1)) >= 0`.
  Invoking `source_window_bound` itself would be circular: it takes all
  restored source rows. MC/MF nonnegativity suffices for the lower bound.
* q^3 divides Y implies q^5 divides U=q^2*Y and Y>=q^3. The actual
  definitions, v<k and c>kY give
  `Dstar>U*a*c-H*k>k*(U*a*Y-H)>0`.
  Apply square-divisibility again to A1=0, obtaining integral positive D
  with Dstar=U*D, `D^2-Delta*c^2=1`, and `U | H*(q*E-v)`.
  `NativePellBootstrap.main_classification` now applies to D,c after casts.
* Free J permits 3 dividing q. The historical proof's exact missing lemma
  is `gcd(q^5,H)=gcd(q,3)`, given q^3 dividing Y and H=4Y(X+1)+3.
  It is 1 or 3 and divides q. For 3 dividing q, H is 3 modulo 27, so
  v_3(H)=1. Consequently `q^5 | H*t` implies `q^4 | t`; apply it to
  t=qE-v and use q^4 dividing qE to get q^4 dividing v. Do not import the
  restricted-J parent's false-in-this-domain premise `gcd(q,H)=1`.
* Generic first/main classification and
  `NativePellBootstrap.main_index_gt_first` give n<p. The latter requires
  the explicit stronger separation `2*A<2*P0-1`, not just P0>A;
  A=Y(X+1)+2, P0=2XY^2+1 and Y>=q^3 discharge it.
* `yn_modEq_a_sub_one` gives k congruent to 2n modulo 4XY^2; q^4 divides
  that modulus. Together with q^4 dividing k-R-1 this gives
  `2*n ≡ R+1 [MOD q^4]`. Positivity and R+1<q^4 give R+1<=2n.
  An exact small adapter of `first_index_lower` should take this ModEq
  directly. The existing theorem instead requires the nonnegative natural
  witness `k=1+R+E*h`; that witness must not be assumed before this step.
* Hence n>=25 and p>=6. Reuse `large_of_six_le` and `twice_index_lt`
  to obtain `c>A*(A^2-1)^2` and `2*p<c`. Also n>=2 gives k>=4P0,
  so `c>kY>8XY^3>=8q^9>2R`. None uses strong/auxiliary equations.

These are all-positive soundness deductions. No canonical-source
completeness assumption, q dividing X, or equality p=R enters them.

## Subsequent transfer boundaries

The existing generic `NativePellStepDown.source_index_of_strong` is useful
only after the preceding main classification and both half bounds. Its
additional premises include the actual strong norm, positive i,f,y, and
**both** integer representations `V=j*c-R` and `V=o*f-c`.

For this graph, strong recovery gives f>=2; c>2R and T>=1 then give
V>c>1, so y=V+u>0. The second representation has
`o=f*(c*T-R)`. The first cannot be asserted from the tail syntax alone:
apply `Jones1980.relaxed_aux` to get
`i*c^2=Delta*yn_A(m)` and f=xn_A(m), hence c^2 divides f^2-1 by the
Pell identity. This supplies the integer j and the required congruence.
Calling `source_index` after this extraction avoids assuming deleted rows.

`NativePellPower.doubled_ratio_lower` is genuinely reusable without a
source. Its later `two_pow_rank_lt_Y` requires X>=16; the adaptive graph
has only X>0 until power recovery. The free-J proof instead splits X>=2
and X=1 and uses congruence modulo H/gcd(q,H). That sharpened ratio/range
argument and the eventual Mersenne factor-3 exclusion still need new Lean
lemmas. `source_X_ge_sixteen`, `source_X_eq_two_pow_rank`,
`source_bootstrap_of_portBox`, and the completed ordinary/shifted-source
adapters cannot be used to bypass these missing steps.

Conversely constructing adaptive positive inputs from current conditional
halting remains a separate task. In particular the adaptive lift
`gamma=gamma_old-w+v/U` needs its own integrality and strict positivity
check against the actual current canonical source. Historical compact44
cofinality is not a current witness premise. The accepted shifted-source
adapter is a downstream endpoint once a genuine positive source exists.

## Cache feasibility and source pins

The companion `adaptive-carrier-bootstrap2011-cache-audit.json` has SHA256
`21917ee6855045afd5c9494868c431f2bd8e2ed67b3ef621e8772f42cdc6b915`.
It records exact source/object hashes and current parsed import equality:

* Sole proposed import `NativePellBootstrap`: **25** reused custom modules,
  **22** actual external boundaries including implicit Init, **66** pinned
  external object companions. No unknown import or hash mismatch.
* Adding a concrete current-port corollary through `CurrentWindowCarry2011`:
  **74** reused custom modules, **41** boundaries, **123** companions;
  again no new boundary or mismatch. This larger import is optional.

The provider is the accepted shifted-source input inventory
`/tmp/native-shifted-source-nm8afaaa/inputs.json`, SHA256
`0e93cd15e178f2f2bbab600734f57edc4412ff5cad19378b60fa623d4b0f1603`.
All selected current sources, cached objects and external source/artifact
bytes were rehashed read-only. This is authenticated cache reuse, not a
new closure build. There is no Foundation dependency or prerequisite
rebuild proposed. Future execution still requires an approved new main/check
pair, a private link overlay, before/after pins, -M6000 -j1, async=false,
and the 512 MiB reserve. No run is authorized by this note itself.

Principal inspected source hashes:

| File | SHA256 |
|---|---|
| free-J `source/positive/p13_free_J.json` | `a6c378ffe706da6ccb17250c31183b0cbff7bdd2c21b85cf0fc393a73bd987b8` |
| free-J `source/positive/PROOF.md` | `4ce1e588973c7f703dea6a3c60ce747f6f0416544a522fe408d7d81a78a08dcf` |
| ordinary `ORDINARY13.md` | `de53d3340d41f0e24b1dfaaded5f166137d44b563f935fb6a4eddaf3bf395dbf` |
| ordinary `README.md` | `8dec2ab7b99257e97cbd3cb9e32f34dcd901e488727f9b7b837943bc5cf1c265` |
| `NativePellBootstrap.lean` | `351d51db7e438b4c9bb8f80f4146df1e9516704c4e47719e562fb9ce9ed521e4` |
| `NativePellStepDown.lean` | `8fc2fb01654786bf8d7a9e104e84593dc43f74f73de53862ff411433fb482814` |
| `NativePellPower.lean` | `91048f3de105e4d24677ed7467aba7231654e1dab31c029fbbec579c2fa10ebe` |
| `CurrentKernelData2011.lean` | `529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c` |
| `CurrentMaskData2011.lean` | `14f32924a514865d4fbd297aac323679c8cfd75305dcc52bb2b588dfffdbdf36` |
| `NativeSourceMask.lean` | `c92d1ee93dff4e8655005bf73d2cedb6ae95a55819c0a14de76202cd0b2a913e` |

This proposed first checkpoint would advance the low-degree route by proving the missing
unbounded carrier divisibility/positivity fact on the full positive domain.
It makes no new equation-size, external consistency-equivalence, or internal
HA/ZFC-equivalence claim.
