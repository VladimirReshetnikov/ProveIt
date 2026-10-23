# Final mathematical consistency review of the research report

Reviewed on 23 October 2026 against ProveIt commit
`4b4349064a750ba6347293b55874a7f92abdd0db`.

## Scope and conclusion

I reviewed `report/report.tex`, its included `short/section.tex`, the selected
coefficient binding and compiler-adapter proof, `nine/PROOF.md`, the reported
degree ledger, and the exact `NineRatio.lean` theorem signatures. This is a
separate mathematical review performed within the same AI-assisted session.
It is not external human review, a new Lean compilation, or a reproof of all
inherited machine/compiler/Pell theorems.

**No mathematical inconsistency was found in the manuscript's new
nine-positive-variable reduction, exact constants, stated degree, CRT
parameter domain, or bounded comparison table.** The intended ordinary
compiler dependency is kept explicit. In particular, the report does not
claim that its local finite audits establish the compiler theorem or an
end-to-end kernel certificate for the new circuit.

The only correction made during this final pass was to the separate
`review/baseline_review.md`, not to the manuscript. Its older discussion had
attributed `f^2 = 1 (mod c)` directly to the ordinary strong equation. That
inference was replaced by the correct canonical normalized completeness
witness transfer. The same note now records the actually materialized
73-operation/degree-54 and 74-operation/degree-46 supplements. The included
short appendix already used the correct argument.

## 1. Source tuple and imported semantics

The principal source is exactly the 22-row, 31-positive-coordinate system
listed in the report appendix. The polynomial source used by packing is
obtained by shifting all 31 coordinates by one. The transport row is the
original positive transport equation; the report does not silently replace
it by the newer shifted transport normalization.

The active binding selects all four ports of the package-31
`wang943-mixed-121x8801` tuple. Its bit lengths are 1,064,921; 1,070,004;
1,064,921; and 1,064,922, with `MF = MF_source` already shifted. The binding
points to the full coefficient adapter, whose stated interface explicitly
includes the positive and signed arithmetic skeletons, rank control,
positive slack, and parity requirements. This is a coherent mathematical
import; port-wise mixing or substituting `MF_native` would not be.

The report correctly treats the final ZFC statement as composition with
the identified ordinary native compiler and K215 calibration. The active
repository's separate closed executable Lean equation does not by itself
certify this materialized circuit. Likewise, an exported derivation inside
the object-language ZFC calculus is not supplied. The current wording
maintains these distinctions.

## 2. Source bounds and the smaller carry code

The constants are internally consistent:

```
Mcoef = 2^2134927
kappa = 2134940
lambda = 2^kappa = 8192 Mcoef
chi = 2^(15 kappa/2 - 11) = 2^16012039.
```

The leading coefficient of the fixed code polynomial is 2 at exponent
5190, so `B - 1 > Mcoef` gives the stated positive lower bound for every
positive `b`. The low mask is nonnegative for all such `b`, independently
of a zero or a bound on `g`. Consequently `R >= L - 1 >= max(8,b)` and
`N >= max(8,b)` hold before invoking the ratio theorem. Deleting the old
leading `L^2` does not invalidate any required size condition.

On `g < 4 b B^183`, the bounds `g < B^184`, `Jcode < B^5557/64`, and
`Scode,Tcode < B^5741/32` imply `Scode + Tcode < L = b B^5741`, including
`b = 1`. The signed coefficient normalization argument is also valid:
`|h_t| < B/8` ensures that carries between signed digits are only 0 or -1;
at a target, a masked digit of 0 or 1 occurs exactly when `h_t = 0`.

For `b = 2^k`, write `v = kappa + 2k` and `u = k + 5741v`. The new two-block
number has

```
pop(R) = u + pop(Tcode) - [pop(Scode)+pop(Tcode)-pop(Scode+Tcode)]
pop(Tcode) = 206v - 31k - 22
u + pop(Tcode) = 5947 kappa + 11864k - 22 = 2 log2(N).
```

Thus the threshold changes by exactly two binary places from the old
sentinel/extra-factor-two construction, and halving its old `chi` is
correct. At `b=1`, the low mask forces `g=0`; positive `g` excludes that
branch. Completeness can always choose a larger power of two. The source
identity `p_5(0)=1` ensures its radix word is positive.

## 3. Ratio hypotheses and the free coordinate

The actual `Jones1982.Nine.ratio_sound` signature requires `R,N >= 8`,
`0 < b <= R,N`, positive capacity and positive `h,s,w,i,j`, with natural
`phi`. It does **not** require `R >= N` or `R > N^2`. The report's imported
interface matches that theorem. The completeness interface needs the
stronger `32g < Gcap`, precisely the bound proved from a source witness.

All majorants are established before recovering a margin or invoking the
ratio theorem. In particular, `A > W`, `D > W^2`, `D > C^2`, and `WC < D`
are valid for the free positive coordinate `C`. The exact identity

```
T_*^2 - 64 D F = (8D+1) k_*^2 - 64D
                  = 8D(k_*^2-8)+k_*^2 > 0
```

holds because `k_* = iJC >= 3`. The positive defect for `V1` and the first
strict majorant therefore hold unconditionally.

The numerator `J(n+W^2)+Q` is strictly positive even when `Q` is negative.
At a norm zero, the real-factor identity and strict majorants first force
`m > 0`. Only then is the old lower bound recovered:

```
C > K(Y-1/2) > 2K >= 2(P+R) > 2R+1+W.
```

This gives positive `phi = C-B1-W` without circularly using the ratio
theorem. Radical separation `a1 > a0` is proved after that step, which
excludes opposite identical nonsquare roots. The nonzero rational sum
then makes each radical rational and hence integral. This order is
essential and is correct in the report.

## 4. CRT parameter and complete witness map

The primary formula is `H = C + F(B1+(j-1)C)` with positive input `j`, so
its internal parameter is `j0 = j-1 >= 0`. The report explicitly includes
and charges this shift.

Since `F = 1 (mod J)` and `F = 1 (mod C)`, the old combined divisibility
is equivalent to `J | Q` and `F | H-C`. The recovered old parameter is

```
j_old = 1 + ((F-1)/C) B1 + F j0 > 0.
```

Conversely, for old witnesses, `(H_old-C)/F` is positive, congruent to
`B1` modulo `C`, and `0 < B1 < C`; this gives a unique nonnegative `j0`.
Thus this reparameterization preserves all required witnesses.

The reconstructed final coordinate

```
n = m(V0+V1+r0+r1) - W^2 - Q/J
```

is integral and positive when positive roots are chosen, because
`W^2+Q/J < 2D < V1`. The proof correctly asserts an existence map, not
that every old final quotient remains positive after subtracting `W^2`.
The analogous `2D+H` bound validates the original-H alternative.

## 5. Exact degree and comparison figures

Independent degree recomputation confirms the main CRT degrees in the
report: `R=22233`, `N=5932`, `A=45963`, `D=91928`, `F=367714`, `G=459643`,
`H=389947`, `a0=320246`, `a1=2158822`, `m=184221`, `Omega=230184`,
`V1=1079411`, and the positive defect `Delta1=1883038`.

In the corrected inner norm, `Omega^2 Delta1` uniquely has greatest degree
2,343,406. Its square therefore has degree 4,686,812, and the subtracted
term `4 Omega^4 a0 a1` has lower degree 3,399,804.

On the common diagonal, write `rho=lambda^11115(lambda+4)` and
`nu=chi lambda^2966`. The leading coefficient is

```
2^94 rho^104 nu^400 lambda^732
 = 2^94 lambda^2343092 (lambda+4)^104 chi^400 > 0.
```

The factor `lambda+4` is necessary: the leading source blocks have equal
degree and both contribute. The report includes it correctly. The degree
also agrees with `104*22233 + 400*5932 + 8*183 + 316`.

The reported 560 operations match the supplied ledger decomposition
`332 + 173 + 55`. The 562-operation original-H and 567-operation natural
translation figures match the same ledger. This review checked those
records, rather than independently rebuilding every gate. The source
identity and gate audits remain the separate finite verification evidence.

The baseline table uses the correct incoming 7,344,328-degree/
738-operation point, retains the cheaper 548-operation/15,502,748-degree
tradeoff, and recognizes the incoming 66-operation short record.
The percentage reductions round correctly to 36.18% and 24.12%.
The two short supplements are correctly described as intermediate
degree/operation tradeoffs, without displacing the 66-operation record or
the degree-44 point. No global optimality or unrestricted-integer result
is implied.

## 6. Short appendix

The appendix agrees with the previously completed separate mathematical
review of `Q54` and `Q46`. Its unconditional minimum blocks, exclusion of
the negative main-norm unit modulo four, and product regrouping are sound.
The squared-modulus completeness step explicitly starts with canonical
normalized witnesses before transferring the ordinary strong coordinate.
This preserves the needed congruence `f^2 = 1 (mod c)` and coprimality;
neither is casually inferred by canceling the discriminant. The declared
leading homogeneous forms and positive coefficient witnesses are
consistent with the literal circuit degree audits.

No further manuscript correction is requested by this review.
