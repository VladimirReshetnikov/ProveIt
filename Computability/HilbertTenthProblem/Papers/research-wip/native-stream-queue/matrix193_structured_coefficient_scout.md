# Structured coefficient evaluation for the 193-matrix packing

The complete saved source has **1,756 gates = 795 multiplications + 961 additions/subtractions**, with the same 150 positive witnesses, ordinary input, eight fixed coefficient ports, twenty outer residuals, native kernel and exact degree 35,587 as the frozen 2,462-gate balanced-output source. This saves **706 gates** by changing only four fixed coefficient-polynomial producers. The complete output polynomials are identical over every commutative ring. No witness change, weaker equation, new simulation premise or new native-history encoding is involved.

The new bound remains much larger than the established 84-gate universal polynomial. This is a source-specific evaluation improvement, with no minimality assertion. It is independent of the separate bounded-high witness chart and the separate controller-hat packing rewrite; neither is included here.

## 1. Pinned source and scope

The companion [checker](matrix193_structured_coefficient_scout.py) reads five pinned predecessor files as inert bytes. Its [receipt](matrix193_structured_coefficient_scout.json) contains the complete 1,756-row source, its full free/witness lists, all four dense coefficient certificates, the 638 live replacement rows and the exact deletion/substitution map. The immediate parent is [balanced output](matrix193_balanced_output_scout.md), not an earlier 3,162- or 4,155-gate source. The fixed word matrices come from [the Gamma1 recoding](matrix193_gamma1_recode.md).

| Inert dependency | SHA-256 |
|---|---|
| `matrix193_balanced_output_scout.py` | `e567a5be0cb656dfc984aa86fb306584dd837b7c24568659af222c781266d76a` |
| `matrix193_balanced_output_scout.json` | `63a4b6b269ba177603cbebec51848bc6fbcd3c04115bb3dbb367dd63a2f7c9bf` |
| `matrix193_balanced_output_scout.md` | `cfc892b2c7a577d2348c3583d968e04ab271f065003cc0bfa6316a9f05f3abde` |
| `matrix193_gamma1_recode.json` | `9cdd0274625c847aa77f5907ba6554ee16f37895f5c026b3d776595330676668` |
| `matrix193_gamma1_recode.md` | `6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742` |

No predecessor Python is imported or executed. The fresh emitter uses the actual 72 upper matrix groups and 96 lower tile groups followed by LOAD. The 193-generator faithful source, its program-dependent fixed contexts, the ordinary-input bridge, positivity recipe, packing converse and native completeness are inherited unchanged through a full polynomial identity. This note does not independently recertify those parent theorems.

## 2. The four polynomial cuts

Write \(\Psi\) for the pinned twenty-letter matrix map, \(v=(Q,1)\), \(t=Q^2\), and \(z=t^3\). For a block with matrices \(M_0,\ldots,M_{N-1}\), define

\[
\mathcal M(t)=\sum_{g=0}^{N-1}M_g t^{N-1-g},\qquad
R_N(t)=1+t+\cdots+t^{N-1}.
\]

The two reverse coefficient words used by the parent convolution are exactly the entries of

\[
v\mathcal M(t)-vR_N(t).
\]

Indeed the two scalar coefficients associated with group \(g\) in column \(j\) are \((M_{0j}-\delta_{0j},M_{1j}-\delta_{1j})\). Reversal places their contribution at
\(t^{N-1-g}[Q(M_{0j}-\delta_{0j})+(M_{1j}-\delta_{1j})]\).

For X, \(N=72\), \(M_g=C_0^{-1}\Psi(h_g)C_0\), where the actual fixed matrix is

\[
C_0=\begin{pmatrix}-31653619&195915076\\-3702035&22913161\end{pmatrix},\qquad \det C_0=1.
\]

Thus the X row is evaluated as
\(vC_0^{-1}\mathcal H(t)C_0-vR_{72}(t)\).
For Y, \(N=97\); the first 96 matrices are \(\Psi(g_g)\), and the final matrix is the fixed LOAD matrix
\(B_0^{-1}=\Psi(((01)^3 11)^2)^{-1}\).
The Y row is \(v\mathcal G(t)-vR_{97}(t)\).
All matrix entries and inverse entries here are fixed integer numerals. Every multiplication by such a numeral in the evaluated source is charged.

## 3. Exact word-triple factorization

Set \(T_0=\Psi(0)\), \(T_1=\Psi(1)\), \(L=\Psi([)\), \(R=\Psi(])\), and

\[
P(t)=T_0t^3+T_1t^2+Lt+R.
\]

The first four groups on both sides are the copy words \(0,1,[,]\). The X groups then contain 22 consecutive triples and two tail groups. The Y groups contain 29 consecutive triples and six tail groups including LOAD. The checker reconstructs these words from the actual tile IDs, authenticates every matrix product, and verifies that all tile IDs merged into an X group have the same word.

For X, ten triples have the right-moving form
\((bp0,bp1,bp0])\).
The other twelve have form
\((p0b,p1b,[p0b)\), six for each written bit \(b\in\{0,1\}\).
Let \(A_R^X(z)\) be the sum of \(\Psi(bp)z^{21-j}\) over the right triples at positions \(j\). Let \(A_b^X(z)\) be the corresponding sum of \(\Psi(p)z^{21-j}\) over the left triples with written bit \(b\). Missing positions have zero coefficient; the original order is preserved. Put

\[
D_{01}=T_0t^2+T_1t,\qquad D_R=T_0t^2+T_1t+T_0R.
\]

Then the entire X triple section is

\[
X_{\rm triple}(t)=A_R^X(z)D_R+
\sum_{b=0}^1\left(A_b^X(z)D_{01}+L A_b^X(z)T_0\right)T_b.
\]

The placement of \(L\) before \(A_b^X\) is essential: the boundary word is \([p0b\), not \(p[0b\). The emitted source pays for both terms. The full upper word polynomial is

\[
\mathcal H(t)=t^{68}P(t)+t^2X_{\rm triple}(t)
+t\Psi(J1)+\Psi(\#).
\]

For Y, fourteen triples are \((qa0,qa1,qa])\), and fifteen are \((0qa,1qa,[qa)\). Define \(A_R^Y(z)\) and \(A_L^Y(z)\) using coefficients \(\Psi(qa)z^{28-j}\) in their respective positions. Then

\[
Y_{\rm triple}(t)=A_R^Y(z)(T_0t^2+T_1t+R)
+(T_0t^2+T_1t+L)A_L^Y(z),
\]

and

\[
\begin{aligned}
\mathcal G(t)={}&t^{93}P(t)+t^6Y_{\rm triple}(t)\\
&+t^5\Psi(0J1)+t^4\Psi(J10)+t^3\Psi(1J1)
+t^2\Psi(J11)+t\Psi(\#)+B_0^{-1}.
\end{aligned}
\]

These are identities in the integer matrix-polynomial ring. They require no determinant, divisibility, positivity or selector specialization. In particular they apply before any native typing or zero-set argument.

## 4. Paid schedule and complete-source identity

The fresh emitter evaluates the sparse matrix-entry polynomials using Horner steps in powers of \(Q^6\), then evaluates the displayed row/matrix formulas. Powers use paid repeated squaring and are reused where already present in the unchanged packing prefix. The already-paid \(R_{72}(Q^2)\) is reused. The parent also supplies \(R_{98}(Q^2)\); the identity \(R_{97}(Q^2)=R_{98}(Q^2)-Q^{194}\) costs two new power multiplications and one subtraction in the emitted schedule. All other emitted additions, subtractions and multiplications are counted, including the constant matrix actions and the final conjugation.

The compiler interns exactly equal univariate integer polynomials in the single cut \(Q\). It may therefore reuse an earlier register when their complete coefficient lists agree. This is a compile-time proof of equality, not a free runtime polynomial evaluation. All 638 emitted component rows are live. The receipt saves these **638 live component gates = 343M + 295A**. A second sparse coefficient interpreter independently expands the emitted source, starting only with \(Q\) as an indeterminate, and compares every coefficient of each of the four outputs with the pinned parent lists.

The old four private Horner cones contain precisely 1,344 rows, with 672M and 672A. Their outputs are replaced as follows:

| Parent output | Replacement output | Degree in Q |
|---|---|---:|
| `r1254` | `cp325` | 143 |
| `r1551` | `cp326` | 143 |
| `r1954` | `cp636` | 193 |
| `r2351` | `cp637` | 193 |

All 1,118 other parent rows are retained. Apart from references to these four cuts, their literal operations and operands are unchanged. The checker verifies that no deleted private row has an external consumer except through the four named cuts. It then treats each proved coefficient pair as a common formal atom and interns the full surrounding parent and child expressions. Every retained register and the final output agree.

Consequently, with exactly the same supplied values,

\[
F_{1756}=F_{2462}
\]

as integer polynomials. Thus all positive zeros, all other zeros, the ordinary-input projection and the fixed coefficient recipe are identical. This also inherits the parent's exact degree 35,587 for every valid fixed recipe; no new dense expansion of that large polynomial is claimed.

| Complete source | M | A | Total | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|
| Frozen balanced parent | 1,124 | 1,338 | 2,462 | 150 | 35,587 |
| Structured coefficient successor | 795 | 961 | 1,756 | 150 | 35,587 |
| Saving | 329 | 377 | 706 | 0 | 0 |

The full new array has 240 distinct integer literals. This statistic is separate from the eight fixed context/recipe ports, whose charged uses remain unchanged. The literal matrices and their products are computed by a finite exact integer recipe from the pinned table; no variable division or input-dependent uncharged computation is introduced.

## 5. Fresh evidence and limits

The fresh receipt records the exact word/group checks, all four complete coefficient expansions, full source topology and liveness, the private-cone audit and the formal whole-output identity. It also compares every retained register, every changed polynomial cut and the final output in 32 signed full-source evaluations over two prime fields. Half use the recorded actual fixed context binding; half vary all fixed ports as well. These finite checks supplement the coefficient and source proofs.

The tiny 302-gate balanced diagnostic does not have the U15 word-triple pattern. Its complete array is carried into the receipt literally unchanged, with a fresh reference evaluation; no saving is attributed to it. The actual 84-cell accepting outer fixture from the parent is recorded expressly as inherited evidence, not rerun or newly materialized here. No giant native Pell witness tuple is claimed.

The standalone commands after installation are:

```sh
python3 "$coefficient_wip/matrix193_structured_coefficient_scout.py" --root "$coefficient_wip" --expect "$coefficient_wip/matrix193_structured_coefficient_scout.json"
python3 -O "$coefficient_wip/matrix193_structured_coefficient_scout.py" --root "$coefficient_wip" --expect "$coefficient_wip/matrix193_structured_coefficient_scout.json"
```

Here `coefficient_wip` is the absolute directory containing the installed packet and its pinned predecessors. The CLI rejects duplicate JSON keys and compares the entire receipt with type-exact equality. Generation uses `--write` instead of `--expect`. All proof guards use explicit exceptions and remain active under `-O`.

Fresh generation and fresh normal and `-O` exact receipt replays from working directory `/` all pass on the frozen helper/receipt. No predecessor script was executed.
