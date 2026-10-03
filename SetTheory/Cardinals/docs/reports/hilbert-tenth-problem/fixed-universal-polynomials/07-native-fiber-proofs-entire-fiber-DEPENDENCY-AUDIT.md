# Entire prescribed-scale native fiber: independent dependency audit

**Result: PASS.** For every valid fixed prescribed-scale AND port tuple, exactly seventeen of the twenty-two positive supplied native coordinates have forced values. The only coordinates that can vary are `f,i,j,o,y_aux`. Replacing those five coordinates changes only comparisons **12, 13, 14** below. Thus thirteen comparisons remain unchanged, not fourteen; fourteen was the corresponding number when only `j,o,y_aux` varied.

This is a deduction from the pinned selector's **forward soundness theorem for every positive solution**, combined with an independent literal-DAG audit. It does not restrict the main auxiliary index to the converse construction's canonical choice, and it does not reprove the inherited relaxed-auxiliary rank theorem.

## 1. Parameters, notation, and exact fixed formulas

Fix valid positive relation arguments `P,Hhat,Mhat,Zhat`, meaning

\[
P=2^\ell\ (\ell\ge0),\qquad H=Hhat-1,\ M=Mhat-1,\ Z=Zhat-1,
\quad 0\le H,M<P,\quad Z=H\mathbin{\mathrm{AND}}M.
\]

The literal circuit computes the following fixed values before its kernel:

\[
q=16P,\quad A_{port}=16H+12,\quad B_{port}=16M+10,
\quad F_3=16Z+8.
\]

Here `F3`, `q`, and both padded input ports are **computed registers**, not additional supplied coordinates. The two port comparisons and checksum force

\[
\begin{aligned}
F_1&=16(H-Z)+4,\\
F_2&=16(M-Z)+2,\\
F_0&=16(P-H-M+Z)-15.
\end{aligned}\tag{1}
\]

The AND hypothesis implies `H+M−Z=H OR M<P`, so `F0≥1`; also `H−Z,M−Z≥0`, so `F1≥4,F2≥2`. Thus these are the unique positive field coordinates. The packing comparison then forces

\[
r=F_0+qF_1+q^2F_2+q^3F_3,\qquad p=2r+1.\tag{2}
\]

Define Pell sequences, for any integer base `T≥2`, by

\[
\chi_T(n)+\psi_T(n)\sqrt{T^2-1}
=(T+\sqrt{T^2-1})^n.
\]

For **every positive native witness**, the following quantities are forced in the displayed order:

\[
\begin{aligned}
X&=2^p,&
Y&=\left\lfloor\frac{(X+1)^{2r}}{X^r}\right\rfloor
  =\binom{2r}{r}+\sum_{v=1}^{r}\binom{2r}{r+v}X^v,\\
w&=X/q,&s&=Y/q,\\
a&=Y(X+1),& A&=a+2,\quad\Delta=A^2-1,\\
E&=XY,& B&=2XY^2+1,\\
c&=\psi_A(p),&d&=\chi_A(p),\\
k&=\psi_B(r+1),&
h&=\frac{k-r-1}{E},\\
\eta&=c-Yk,&\zeta&=k-\eta=(Y+1)k-c,\\
\mathrm{ga}&=\frac{d-X-ac}{4a+3},&
\tau&=\frac{\chi_B(r+1)-1}{2},\\
\mathrm{odd\_half}&=(s-1)/2,&
\mathrm{bound\_beta}&=X-r.
\end{aligned}\tag{3}
\]

**Count.** The seventeen fixed supplied coordinates are

`F0,F1,F2,r,w,s,a,c,d,k,h,eta,zeta,ga,tau,odd_half,bound_beta`.

`X,Y` are computed registers (`wq,sq`). Therefore a list asking for formulas for these seventeen coordinates *and* `X,Y` has nineteen names without making nineteen supplied coordinates fixed.

### Why these formulas apply to every positive witness

1. The port and checksum equations alone prove (1); packing proves (2). This uses neither a canonical witness nor any Pell inference.
2. Selector §2, equations (4)–(5), proves universally that the main Pell index is `p=2r+1`, so `c=ψ_A(p),d=χ_A(p)`. The same section proves that the first norm's index is exactly `r+1`, so `k=ψ_B(r+1)`. Its temporary first-Pell-base symbol `P` is renamed `B` here to distinguish it from the external prescribed-scale parameter.
3. Selector §3 proves `X=2^(2r+1)` and exactly the displayed rounded binomial expression for `Y` in every positive solution. This step is essential: merely presenting the converse construction would not prove uniqueness. Together with (1)–(2), these universal conclusions force `X,Y,a,A,B,c,d,k` without dependence on `f,i,j,o,y_aux`.
4. The equalities `X=wq,Y=sq`, and comparisons 3, 4, 6–10 below, now force `w,s,h,eta,zeta,ga,odd_half,bound_beta` by direct division or subtraction. Their denominators `q,E,4a+3` are positive.
5. The first norm gives
   \[
   (2\tau+1)^2-4(E^2+X)Y^2k^2=1.
   \]
   Since `4(E²+X)Y²=B²−1` and `k=ψ_B(r+1)`, the positive square root is `2tau+1=χ_B(r+1)`. This proves the displayed formula for `tau`; the negative quadratic root is excluded by positivity. Equivalently, `t↦t(t+1)` is strictly increasing for positive integer `t`.
6. Valid ports admit at least one strictly positive extension by the pinned prescribed-scale projection/converse theorem. Consequently all quotients in (3) are integral and positive. They are the same in every extension. This argument does not assume that arbitrary proposed numbers in (3) automatically satisfy the auxiliary subsystem.

No one of the displayed formulas uses the variable auxiliary index `m` or the normalized auxiliary index. Conversely, the constraints on the free five still depend on fixed `A,c,p`; “free” means the only potentially varying coordinates, not independent unrestricted integers.

## 2. All sixteen literal comparisons

Set `U=jc−p` and `R=ic²`. Residuals are written as their literal left side minus right side, up to the displayed rearrangement of zero. The incidence column records transitive dependence on the five potentially varying coordinates in the original DAG.

| No. | Exact comparison | Five-coordinate incidence |
|---:|---|---|
| 1 | `r = F0+qF1+q²F2+q³F3` | none |
| 2 | `F0+F1+F2+F3+1 = q` | none |
| 3 | `s = 2 odd_half+1` | none |
| 4 | `r+bound_beta = X` | none |
| 5 | `(E²+X)(Yk)² = tau(tau+1)` | none |
| 6 | `c = Yk+eta` | none |
| 7 | `k = eta+zeta` | none |
| 8 | `k = r+1+hE` | none |
| 9 | `a = Y(X+1)` | none |
| 10 | `d = X+ac+ga(4a+3)` | none |
| 11 | `d² = 1+Delta c²` | none |
| 12 | `(ic²)² = Delta(f²−1)` | `f,i` |
| 13 | `(ic²)²(U²−y_aux²) = 1−y_aux²` | `i,j,y_aux` |
| 14 | `U = of−c` | `f,j,o` |
| 15 | `F1+F3 = 16H+12` | none |
| 16 | `F2+F3 = 16M+10` | none |

Comparison 12 is the **main auxiliary norm**, not comparison 11 (the fixed main Pell norm). The parenthesization `Delta*(f²−1)` is the corrected literal source expression; replacing it by `Delta*f²−1` is wrong. Comparison 13 is equivalent to

\[
(RU)^2-(R^2-1)y_{aux}^2=1.
\]

On fixing all seventeen coordinates to (1)–(3), the entire twenty-two-coordinate positive fiber is therefore **exactly** the positive five-tuples satisfying comparisons 12–14. Necessity is immediate. For sufficiency, the other thirteen residuals retain their zero values, and all recomputed registers are deterministically obtained by the unchanged acyclic DAG. No extra gate, residual, or hidden positivity obligation is introduced: the stipulated positive domain is on the twenty-two supplied coordinates, and computed subtraction registers are governed by the same literal circuit.

Coordinate-wise incidence is exactly

- `f → {12,14}`
- `i → {12,13}`
- `j → {13,14}`
- `o → {14}`
- `y_aux → {13}`

This is an identity-level dependency result on arbitrary supplied assignments. Some numerical changes can leave a residual's value unchanged accidentally, which does not change its polynomial dependence.

## 3. Independent mechanical evidence

The independently authored script `audit_dependency.py` reads only the pinned JSON data. It does **not** import or execute author Python. For each of the four retained fixtures (`incdec,zero3,nop,positive3`) it independently:

- checks the single-assignment 64-gate source is acyclic in its supplied order
- symbolically evaluates every gate using the actual external leaves
- expands and compares all sixteen literal residuals against the independent formulas in §2
- propagates transitive source dependencies, also checking that these agree with the actual free symbols of the expanded residuals
- checks the witness list has twenty-two distinct supplied coordinates and precisely seventeen outside the free-five set

All checks passed. The four fixtures use different outer leaves and some fixed zero output ports, but each preserves the same sixteen-comparison native template. The general prescribed-scale interface comes from the pinned Markdown theorem, rather than from extrapolating a finite fixture test.

Machine-readable evidence: `DEPENDENCY-RECEIPT.json`. The script resolves `source/native_blocks.json` relative to its own location and verifies the pinned SHA-256. Default replay is read-only and compares its computed receipt to the saved receipt; only explicit `--write` creates or updates that receipt. From this research directory, run:

    python audit_dependency.py
    python -O audit_dependency.py

Both modes passed after hardening. Every scientific check uses explicit runtime validation rather than an `assert`, so optimization does not disable tests. Three in-memory failure-mutation tests also run in both modes: replacing `Delta*(f²−1)` by `Delta*f²−1` is rejected at comparison 12, removing the `o` dependency is rejected at comparison 14, and changing the declared supplied witness list is rejected. The source files are never modified by these tests.

This verifies literal arithmetic identities and dependency incidence. Universal uniqueness additionally uses the source's stated forward Pell soundness, as made explicit in §1. No astronomical complete witness was materialized.

## 4. Sources and provenance

All upstream sources are pinned to commit `ad634b2d10ad666260f9fdff04ec94b75169ee4b`.

- [Selector theorem](https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_binary_selector56.md), §2 equations (4)–(5) and index recovery, §3 equations (6)–(10), §5 converse. Local lines 64–139 provide the universal forced-index, exponent, and rounding conclusions. SHA-256: `97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c`.
- [Prescribed-scale AND interface](https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_binary_masked_selection63.md), §2 equation (4): exact scale/port projection and unchanged twenty-two-coordinate positive domain. SHA-256: `c2e08f2d9fdaaf2e17880d7a131254492afd7ef21b035985714734cbc158c53e`.
- Frozen JSON: `source/native_blocks.json`, SHA-256 `a3ef38c5a449040a817384d564da90a5b7a440d426997df8ae6acecc4d55d74f`.
- Prior local slice theorem: `the earlier fixed-slice theorem (historical context; the required argument is restated in the entire-fiber theorem §4)`, §§1–4. Its two-progression classification applies after `f,i` are fixed; the present audit establishes the missing reduction from twenty-two supplied coordinates to five potentially varying ones.

Only new files in the requested research directory were written. Frozen inputs and public artifacts were not modified.

## Portable release note

The delivered audit uses exact sparse integer-polynomial arithmetic from the Python standard library. It preserves all sixteen residual comparisons on all four fixtures and all three negative scientific mutations. Its regenerated receipt identifies this implementation. The original symbolic audit was reviewed before this packaging adaptation.
