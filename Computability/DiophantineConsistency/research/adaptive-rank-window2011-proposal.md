# Adaptive target window and early Pell-index bounds

This read-only proposal is the next checkpoint after accepted
`NativeAdaptiveMainBootstrap`. Suggested files are
`NativeAdaptiveRankWindow.lean` and Checks, importing only that frozen
main. No new proof source, compiler run, generator, equation metric, or
full adaptive equivalence is supplied here. The proposed endpoint derives
the target window, the first/main index comparison, and all three early
large-c/half bounds before strong-index or power recovery.

## Exact inputs and current coefficient contract

Continue to use the literal unrestricted-J cuts:

```
q=beta*J+1, C=q-F-alpha,
Bt=(q*K+X)*C-q*F, ell=X*k*Y^2,
R=NativeAdaptiveMainBootstrap.target q F alpha J MC MF,
v=k-R-1, Q=X*Y^2, P=2*Q+1,
a=Y*(X+1), A=a+2, c=k*Y+eta, Delta=A^2-1.
```

The actual input tuple has k=eta+zeta and all thirteen inputs positive.
This checkpoint only needs the weaker k>0 and eta>0. The first carrier
uses `firstA0 q ell k r Y Bt=0`; the second uses the accepted literal
`mainA1 q X Y k eta gamma v=0`. In the actual array
ell=(X*Y)*(k*Y), so its equality with X*k*Y² is a ring identity.
No index or source coordinate is silently substituted into either norm.

Use `NativePellBootstrap.PortBox ports` for beta=ports0, K=ports1,
MC=ports2 and MF=ports3, and **explicitly add 15<=ports0**. PortBox
alone supplies only beta>0 and is not claimed to imply the numerical
first-index bound 25. The actual current 47313-byte tuple discharges both
through

```
CurrentWindowCarry2011.interface.portBox
CurrentWindowCarry2011.interface.beta_ge_fifteen.
```

Its MF is already highPort+beta, exactly once. J is positive and otherwise
unrestricted. No condition modulo 3, Mersenne-power recovery, coprimality,
or historical compact44 calibration is used. A concrete current-port
corollary need not be imported in this small generic leaf.

## 1. Literal target window, without a source

The first carrier and its transport lemma already derive q³|Y and C>0.
Given J,F,alpha>0 and the port box, q>=16. Put
G=(q-1)(q-F)+alpha. The identity

```
G-q=(q-1)*(q-F-1)+(alpha-1)
```

shows G>=q. Nonnegative masks imply R>=q(q²-1)>3q.
For the upper bound use the exact identity already visible in the proof
of `source_window_bound`, but prove it directly for the target polynomial:

```
q^4-q^3-q-1-R
 = q*(q^2-1)*(F-1)+(q^2-1)*(C-1)+(q+1)*(J-1)
   +J*((beta-MC-1)+q*(2*beta-MF-1)).
```

Every summand is nonnegative under the listed hypotheses. It follows that

```
3*q < R <= q^4-q^3-q-1 < q^4-2,
0 < R+1 < q^4.
```

The equality q=beta*J+1 is necessary to the upper identity and must
remain explicit in the helper. Neither `source_window_bound` nor
`source_rank_gt_three_q` can be invoked: both require the complete
restored source and would be circular here. Their elementary target
algebra is reusable without their source hypotheses.

Proposed precise helper:

```lean
theorem target_window (ports : Fin 4 → ℤ)
    (hports : NativePellBootstrap.PortBox ports) (hbeta : 15 ≤ ports 0)
    {J F alpha q : ℤ} (hJ : 0 < J) (hF : 0 < F) (halpha : 0 < alpha)
    (hq : q=ports 0*J+1) (hC : 0 < q-F-alpha) :
    16 ≤ q ∧
    3*q < NativeAdaptiveMainBootstrap.target q F alpha J (ports 2) (ports 3) ∧
    NativeAdaptiveMainBootstrap.target q F alpha J (ports 2) (ports 3)
      ≤ q^4-q^3-q-1
```

The strict window is then a short arithmetic consequence. K is unused by
this helper; its nonnegativity is used when deriving C from transport.

## 2. First classification and the index residue

The accepted A0 theorem gives a signed tau with
tau²=ell(ell+k)+1. Substitute ell=Q*k and expand:

```
tau^2=1+Q*(Q+1)*k^2.
```

Apply `NativeAdaptiveCarrierBootstrap.classify_signed_first_norm`.
It returns n>0, |tau|=xn_P(n), and k=2yn_P(n). The sign of tau
remains unrestricted. A1 independently returns positive D and p>0 with
D=xn_A(p), c=yn_A(p), and q⁴|k-R-1.

Write Y=q³s with s>0, as already derived. Then

```
2*Q=2*X*Y^2=q^4*(2*X*q^2*s^2),
```

so q⁴ divides P-1=2Q. The generic
`Pell.yn_modEq_a_sub_one` says yn_P(n) is n modulo P-1.
`Nat.ModEq.of_dvd` reduces this to q⁴; multiplying the two sides by 2
gives k congruent to 2n modulo q⁴. No stronger scaled-modulus assertion
is necessary. Combine this with the **signed** divisibility
q⁴|(k-R-1) to get 2n congruent to R+1 modulo q⁴.

The existing `NativePellBootstrap.first_index_lower` is not directly
usable: it assumes a natural h with k=1+R+E*h. Such a nonnegative witness
has not yet been proved. The smallest replacement takes signed divisibility:

```lean
theorem first_index_residue_of_dvd {E Q k n R : ℕ}
    (hQ : 0 < Q) (hEP : E ∣ 2*Q)
    (hk : k=2*Pell.yn (by omega : 1 < 2*Q+1) n)
    (hind : (E : ℤ) ∣ (k : ℤ)-(R : ℤ)-1) :
    2*n ≡ R+1 [MOD E]

theorem first_index_lower_of_dvd {E Q k n R : ℕ}
    (hQ : 0 < Q) (hEP : E ∣ 2*Q) (hR : R+1<E)
    (hk : k=2*Pell.yn (by omega : 1 < 2*Q+1) n)
    (hind : (E : ℤ) ∣ (k : ℤ)-(R : ℤ)-1) : R+1 ≤ 2*n
```

`Nat.modEq_iff_dvd` has exactly the signed conclusion
`(E:Z) | b-a`; it supplies `(R+1) ≡ k` without a sign assumption on
their difference. To prove the lower bound, assume 2n<R+1<E.
`Nat.ModEq.eq_of_lt_of_lt` then identifies the two canonical residues,
a contradiction. Positive k,R,Q,q are cast to naturals only after their
positivity is established; the signed difference is preserved during
that cast. No integer quotient has been assumed nonnegative.

Since q>=16 and R>3q, R+1>=50. Thus R+1<=2n gives n>=25.

## 3. The stronger base separation and main index

The reusable theorem `NativePellBootstrap.main_index_gt_first` requires
**2A<2P-1**, not merely P>A. For X>=1 and Y>=2 the exact gap is

```
(2*P-1)-2*A
 = (X-1)*(4*Y^2-2*Y)+(Y-2)*(4*Y+4)+5 > 0.
```

All terms preceding +5 are nonnegative. The natural subtraction in 2P-1
is justified by P>1 before the signed ring identity is transported back.
Also c=kY+eta>k and c>1, since k,eta>0 and Y>=2. These facts discharge
every generic premise:

```lean
NativePellBootstrap.main_index_gt_first {A P c k p n : ℕ}
  (hA : 1<A) (hP : 1<P) (hc : 1<c)
  (hp : 0<p) (hn : 0<n) (hAP : 2*A<2*P-1)
  (hcp : c=Pell.yn hA p) (hk : k=2*Pell.yn hP n)
  (hkc : k<c) : n<p
```

It follows that p>=26, in particular p>=6. This is before any strong
norm, step-down, p=R, or odd-rank conclusion.

## 4. Large c and both half bounds fit the same checkpoint

Two accepted generic lemmas now apply directly:

```lean
NativePellBootstrap.large_of_six_le {A c p : ℕ}
  (hA : 1<A) (hp : 6≤p) (hcp : c=Pell.yn hA p) :
  A*(A^2-1)^2<c

NativePellBootstrap.twice_index_lt {A c p : ℕ}
  (hA : 1<A) (hA3 : 3≤A) (hc : 1<c)
  (hcp : c=Pell.yn hA p) : 2*p<c
```

The second half bound needs no q^9 growth estimate. The actual generic
`Pell.yn_ge_n` gives n<=yn_P(n). Therefore

```
R+1 <= 2*n <= k,
c=k*Y+eta > 2*k >= 2*(R+1) > 2*R.
```

This also establishes v=k-R-1>=0, but only **after** the modular-index
argument. It must not be used to justify that argument in reverse.
There is no need yet to claim v>0 or a positive restored quotient.

## Recommended public bundle and stopping point

The helper results should be composed with the accepted A0 and A1
theorems, so the public endpoint assumes the literal carrier equalities
rather than asking its caller for the desired index relations. For
readability the displayed cut equations can be explicit equalities:

```lean
theorem adaptive_early_bounds (ports : Fin 4 → ℤ)
    (hports : NativePellBootstrap.PortBox ports) (hbeta : 15≤ports 0)
    {J F alpha X Y k eta gamma r q R Bt : ℤ}
    (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha)
    (hX : 0<X) (hY : 0<Y) (hk : 0<k)
    (heta : 0<eta) (hgamma : 0<gamma) (hr : 0<r)
    (hq : q=ports 0*J+1)
    (hR : R=NativeAdaptiveMainBootstrap.target q F alpha J (ports 2) (ports 3))
    (hBt : Bt=(q*ports 1+X)*(q-F-alpha)-q*F)
    (h0 : NativeAdaptiveCarrierBootstrap.firstA0 q (X*k*Y^2) k r Y Bt=0)
    (h1 : NativeAdaptiveMainBootstrap.mainA1 q X Y k eta gamma (k-R-1)=0) :
    let A := Y*(X+1)+2
    let Q := X*Y^2
    let c := k*Y+eta
    3*q<R ∧ R+1<q^4 ∧
    ∃ n p : ℕ, ∃ D : ℤ,
      25≤n ∧ n<p ∧ 6≤p ∧ 0<D ∧
      k=2*(Pell.yn (by
        have hQ : 0<Q := mul_pos hX (pow_pos hY 2)
        omega : 1<2*Q.toNat+1) n : ℤ) ∧
      NativeAdaptiveMainBootstrap.mainDstar q X Y k eta gamma (k-R-1)=q^2*Y*D ∧
      D=(Pell.xn (by omega : 1<(Y*(X+1)).toNat+2) p : ℤ) ∧
      c=(Pell.yn (by omega : 1<(Y*(X+1)).toNat+2) p : ℤ) ∧
      A*(A^2-1)^2<c ∧ 2*(p:ℤ)<c ∧ 2*R<c
```

The bounds and classifying indices refer to the same k,c and D as the
actual two carriers. A small internal cast helper may keep the finite
natural bookkeeping separate, but must not strengthen the public premises.
No original source row, rank binding, oddness, strong norm, auxiliary norm,
or canonical witness is allowed as an extra input.

Freeze after this bundle. Later tasks are still strong-index recovery,
the first-index equality and parity, power recovery with free-J factor 3,
ordinary integrality and positivity restoration, the canonical converse,
and the final whole-polynomial/current-port equivalence. The historical
ordinary proof and the accepted source adapters cannot replace these steps.

## Cache feasibility and read contracts

The sole proposed import is `NativeAdaptiveMainBootstrap`. Its accepted
root overlay is `/tmp/native-adaptive-main-root-9pp4_mhm/lib`, with ROOT
SHA256 `65988589bee87bebfc0ccae84b3eafa6277d3bc95c650ddbe4d99500cca55824`.
The selected closure is **28 cached custom modules**, the unchanged
**22 actual external boundary names including Init**, and **66 external
artifact companions**. No Foundation module, new boundary, or prerequisite
build is proposed. A future authorized run would compile only the new
main and Checks with the same caps and 512 MiB guard.

All selected current source/object pairs and every actual external source
and artifact were rehashed read-only; the closed custom import names were
checked. The exact audit is
`adaptive-rank-window2011-cache-audit.json`, SHA256
`6419ec8955372535c1855c00c926762472d714fc607002acd11a1c783d22facd`.
The current-port interface is read as a known later specialization, not
added to this small import closure. `NativePellScaleBounds` and
`NativePellFirstIndex` were inspected for their precise source-dependent
contracts, not imported or treated as source-free theorems.

Principal source pins:

| File | SHA256 |
|---|---|
| NativeAdaptiveMainBootstrap.lean | `a735876afcc033877741f414e233f1dea1bc9209899979fd83fc8308733eae7a` |
| NativePellBootstrap.lean | `351d51db7e438b4c9bb8f80f4146df1e9516704c4e47719e562fb9ce9ed521e4` |
| NativePellScaleBounds.lean | `9a2716b017ebf1fd35042e233a165e80d44924c1a6ce09bb6cbe7f37e1b365b3` |
| NativePellFirstIndex.lean | `85d97f1e1f81cfc1d096b3148d77d6f155b845fe089f774e0424ac1e914387c5` |
| NativeSourceMask.lean | `c92d1ee93dff4e8655005bf73d2cedb6ae95a55819c0a14de76202cd0b2a913e` |
| CurrentWindowCarry2011.lean | `2ac2ddb722b7b23c7d528252da28d65486c551dc86d07f22eabbdb19e4a1b39e` |
| Mathlib/Data/Nat/ModEq.lean | `678c7d5030c056efb633aaab3a1b44ceec599332b9f70f694b08f4cce27d1fea` |
| Mathlib/NumberTheory/PellMatiyasevic.lean | `a8ea2ddf5167a9163f3af19309eed96213848b632b58f8e5857535b3a1412341` |

The controller independently challenged only the displayed base-gap
identity and the modular lower-bound/yn_ge_n half-bound argument, finding
no arithmetic issue. This is not an independent source or compiler review.
No new equation-size, external consistency, or internal HA/ZFC endpoint
is claimed by this proposal.
