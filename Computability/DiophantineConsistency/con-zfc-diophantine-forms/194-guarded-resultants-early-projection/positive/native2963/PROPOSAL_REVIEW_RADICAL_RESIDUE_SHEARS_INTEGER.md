# Integer review: polynomial shears and radical residue

Reviewed 2026-10-23, while Lean formalization is paused. The new integer reductions are sound in ordinary arithmetic on the stated inherited source interface. I found no missing parity condition, division hypothesis, or substitution of an incompatible coefficient tuple. This review covers the integer components only. It does not establish the inherited native-machine calibration anew or supply a Lean proof or a derivation inside object-language ZFC.

The two incoming archives are pinned by SHA-256:

| Archive | SHA-256 |
|---|---|
| `ConZFC_Polynomial_Shears_2026-10-23.zip` | `978f7e8be846732c1330f3a75a0fe38871432f79951b8eaad6ef096f3e03e165` |
| `con-zfc-radical-residue-2026-10-23.zip` | `7d10ee7e2186b82d660d218137added7a14e3463390845fc37e1228eddbd9394` |

Extraction inventory: `/tmp/dioph-wave11-arrivals-440dd03ab8/ARRIVALS.json`. The third archive in that inventory, saturation and projection, is outside this review.

## Results and count convention

All variables below range over unrestricted integers. Fixed coefficients have degree zero. Binary additions, subtractions, and multiplications count as one operation each, including squarings. Fixed numeral leaves are free. The operation counts below are for supplied literal live DAGs; I have not assigned counts to packets lacking a supplied DAG.

| Packet | Variables | Exact degree | Live operations | Comment |
|---|---:|---:|---:|---|
| shears `centered23_degree10` | 23 | 10 | — | Eleven squared residuals; two polynomial coordinate eliminations and norm translations. |
| shears `pivot21_degree16` | 21 | 16 | — | Monic transport pivot. |
| shears/radical `pivot20_degree20` | 20 | 20 | — | Same pivot on the next parent. |
| shears/radical `pivot19_degree32` | 19 | 32 | — | Same pivot. |
| shears/radical `pivot18_degree88` | 18 | 88 | — | Same pivot; parent of the radical construction. |
| radical `norm17_degree112` | 17 | 112 | **124** | 68 multiplications, 29 additions, 27 subtractions. |
| radical `norm17_degree110` | 17 | 110 | **140** | 80 multiplications, 33 additions, 27 subtractions. |
| radical `center18_degree80` | 18 | 80 | **115** | 60 multiplications, 30 additions, 25 subtractions. |

All gates, all variables, and all six coefficient ports in those three DAGs are live. The independent AST upper bounds and an exact univariate finite-field specialization using the actual coefficient bytes confirm the displayed total degrees. The source proofs also supply uniform nonzero distinguished coefficients, discussed below.

The already reviewed Pell-congruence archive supplies 17Z/88 and 18Z/32. Thus the new radical points do not improve the variable/degree frontier. They supply explicit circuit tradeoffs; a full comparison including operations requires comparable circuits for the lower-degree points. In particular, 17Z/110 does not dominate 17Z/112 because it costs sixteen more operations. The shears 23Z/10 and 21Z/16 improve their respective inherited 24Z/10 and 22Z/16 points by one variable.

## Whole tuple and source identity

Both components carry the identical six coefficient numerals: the entire source-34 tuple with `beta = 2^1064921 - 1`, its matching `K0`, `MC`, and **already beta-shifted** `MF`, and `cone_A = 2^1113`, `cone_B = 2^666104`. Their decompressed payloads total 615,883 bytes. The raw bytes also match the whole tuple in the preceding Pell-congruence integer review. No compact44 or compact54 port is substituted.

Both reductions pin the incoming Joint Guards source at commit `c1a102936aca437e9999530a0111e6ddab56dc6d`, archive SHA-256 `291af5f4266ba5e0759273282ef4c6c5941f0bd2c3813e0481b721b08605b159`. The stored parent JSON and proof hashes authenticate correctly. The two packages' pivot packets implement the same coordinate transformations from those parents. Literal filenames and metadata need not be byte-identical for that semantic statement; the parent rows and maps are checked algebraically by the selected author checks.

The inherited source retains the transport equation

\[
(K_0+W)C-F-z(q-1)=0,\qquad C=q-F-\alpha.
\]

This is the already shifted source convention. It must not be identified with the earlier old-z equation without translating both the coefficient/transport convention and its integer-domain interface. The new eliminations work directly with the pinned row; they introduce no positivity restriction on the restored `z`, `F`, or `alpha`.

## Polynomial shears: exact zero-set maps

The main 23-variable packet starts from the pinned 25-variable octic Joint Guards packet. Use

\[
Y=a-E,\quad k=\eta+\zeta,\quad c=Yk+\eta,\quad V=fo-c,
\quad T=E(c-\eta),\quad H=4a+3.
\]

Translate the old root variables by `tau_old = tau + T` and `y_old = V + nu`. The first norm and auxiliary norm become, identically,

\[
\begin{aligned}
(\tau+T)^2-T(k+T)-1&=\tau^2+(2\tau-k)T-1,\\
I^2V^2-(I^2-1)(V+\nu)^2-1&=(V+\nu)^2-I^2\nu(2V+\nu)-1.
\end{aligned}
\]

The main norm cancellation is

\[
(ac+S)^2-(a^2+H)c^2-1=2acS+S^2-Hc^2-1,
\qquad S=X+\gamma H.
\]

The old rank-derived `k0` need not equal `k` away from the zero set. The construction correctly retains their difference. If `B1,...,B11` denote the new residuals in literal order, let `L = B10 = k-k0`. After the displayed coordinate substitutions, the thirteen old rows are exactly

\[
B_1,B_2,Y L,B_3+T L,B_4,B_5-L,B_6,0,B_7,B_8,B_9,L,B_{11}.
\]

This is the key check against an invalid off-zero replacement of `k0` by `k`. Keeping `L` makes both directions valid by row operations. The eliminated `c,V` and translated roots restore by integer polynomials. No division, Pell theorem, or cofinal witness adjustment is needed for this local equivalence.

The residual upper degrees are `4,3,4,5,4,2,5,4,5,3,4`. The coefficient of `r^2 a^4 eta^4` in the squared system is exactly 4, so the actual specialized polynomial has degree 10.

For each transport-pivot companion, first replace `alpha` by `C`, then solve the monic equation for `F`:

\[
F=(K_0+W)C-z(q-1),\qquad\alpha=q-F-C.
\]

The coefficient of `F` in its defining transport row is -1. Consequently the elimination remains valid even if `K0+W=0`; no invertibility assumption on that expression is involved. Every occurrence, including the determinant guard and packing rank, is substituted. The exact rank identity

\[
(q-1)(q-F)+\alpha=q(q-F)-C
\]

keeps the restored packing expression consistent. This removes one variable and one row on every zero set, with a polynomial inverse on that set. The first companion has the unchanged degree-16 witness `a^4 f^8 o^4` of coefficient 1. The remaining companions' degree certificates likewise survive the pivot, and the substituted guard/rank do not increase the claimed degrees.

## Radical merger: hypotheses obtained before the removed roots

The compact 18-variable parent has six rows

\[
\tau^2-A,\quad (X+ac+\gamma H)^2-\Delta c^2-1,
\quad cj-V-R,\quad Q-\Delta(f^2-1),
\quad QV^2-(Q-1)y^2-1,\quad G,
\]

where

\[
\begin{gathered}
q=\beta(3J_3+1)+1,\quad W=4(3w_3+1),\quad X=qW,
\quad Y=(2v+1)q^3,\quad E=XY,\quad a=(X+1)Y,\\
V=fo-c,\quad k=1-V+jc+hE,\quad\eta=c-Yk,
\quad u=EYk,\quad A=u(u+k)+1,\\
I=(2r+1)c^2,\quad Q=I^2,\quad
G=d\,\eta(k-\eta)-(p^2-d-\eta(k-\eta)+1)^2-\mathrm{Pos},\\
\mathrm{Pos}=1+p_1^2+p_2^2+p_3(p_3+1)>0.
\end{gathered}
\]

The guard `G=0` forces `d>0` and `eta(k-eta)>0`. The negative/negative alternative is impossible: writing them `-b,-e` gives a square at least `(b+e+1)^2 > be`. Thus `|k|>=2` and `0<|eta|<|k|`. Since `J=3J3+1`, `3w3+1`, and `2v+1` are all nonzero, the literal beta gives `|q|>=16` and `|Y|>=16^3`. Hence

\[
|c|=|Yk+\eta|>(|Y|-1)|k|>1,
\]

so `I` is nonzero and `Q>1`. Finally `u=bk` for the integer `b=XY^2`, whence `A=b(b+1)k^2+1>=1` even when some coordinates are negative.

These are genuinely early hypotheses: their derivation does not use either discarded root row, late native rank recovery, or positivity of the unrestricted coordinates.

## Why the resultant recovers integer roots

Write `delta=Q-1`, `Bnum=QV^2-1`, and introduce one unrestricted integer `xi` instead of `tau,y`:

\[
\begin{aligned}
L&=\xi^2+2I(2u+k)\xi+Q(k^2-4),\\
N&=(\delta L-4Bnum)^2-64\delta QA\,Bnum.
\end{aligned}
\]

Completeness uses the integral assignment `xi=2(I tau+y)-I(2u+k)`. For soundness set, in the proof only,

\[
s=(I(2u+k)+\xi)/2,\qquad B=Bnum/\delta.
\]

The exact identity is

\[
N=16\delta^2\big((s^2-QA-B)^2-4QA B\big).
\]

Since `QA>0`, the equation implies `B>=0`; `B=0` would give `QV^2=1`, impossible for integral `Q>1`. Also `QA=B` would imply the integer identity `Q[(Q-1)A-V^2]=-1`, impossible. Thus `s!=0`, and

\[
x=(s^2+QA-B)/(2s),\qquad y=(s^2-QA+B)/(2s)
\]

are rational with `x^2=QA` and `y^2=B`. Now `tau=x/I` is rational and has square the integer `A`, so it is integral. To make `y` integral one needs the adjacent-coefficient Pell descent, rather than a generic resultant claim.

Here is the denominator argument used in the supplied proof. If `y=a/m` is in lowest terms and `QV^2-(Q-1)y^2=1`, then `m^2 | Q-1`. For `|V|>1` take positive absolute values and transform

\[
V'=(2Q-1)V-2(Q-1)y,\qquad y'=(2Q-1)y-2QV.
\]

The first coordinate is integral, the norm is preserved, and `-V<V'<V`, using `y>V` and `QV>(Q-1)y`. The latter follows by squaring, because `Q^2V^2-(Q-1)^2y^2=QV^2+Q-1>0`. The reduced denominator of `y'` remains exactly `m`, since `2Q-1` is 1 modulo `m`. Norm preservation excludes `V'=0`; descent reaches `|V|=1`, where `|y|=1`. Therefore `m=1`. This restores the auxiliary root integrally.

The factor `I` on the first root is essential. Without it, the two radicands may agree nonsquare and the zero sum of opposite irrational roots can be an integer. The supplied negative control `Q=4,V=2,A=5` exhibits this failure for the unscaled merger; the scaled radicands are 20 and 5 and reject it. No parity restriction on `xi` is omitted: the recovered integral roots imply the required parity afterwards. The actual polynomial contains no division.

The highest form of `N` is

\[
-2^{26}3^{26}\beta^{22}
r^6c^{12}h^2f^2o^2J_3^{22}w_3^4v^6.
\]

The other rows have smaller degree, so the sum of squares has the corresponding degree-112 coefficient `2^52 3^52 beta^44`, nonzero for the actual numeral.

## The degree-110 shear and degree-80 midpoint variant

The 17Z/110 packet is an integral coordinate shear `xi_old=xi_new+2V`. Its factored polynomial expands **identically** to `N(xi+2V)`; the cancellation uses `(2u+k)^2=4A+k^2-4`. Thus it preserves integer solutions in both directions without any new arithmetic hypothesis. Its degree-110 leading coefficient is again `2^52 3^52 beta^44`, now with the `f^2 o^2 xi^2` monomial rather than `f^4 o^4`. The larger literal DAG realizes the reported degree/operation tradeoff.

The 18Z/80 packet instead replaces the first root row by

\[
M=t^2+2(2u+k)t+k^2-4.
\]

With `t=2tau-2u-k`, this is `4(tau^2-A)`. Conversely `M=0` implies `(t+k)^2=0 mod 4`, so `t+k` is even and `tau=(t+2u+k)/2` is an integer. This is a valid parity-free polynomial replacement of the old root variable.

Let `S` be the sum of squares of the other five arithmetic rows, including `M`, while keeping `G` unsquared. The finalizer is `(1+G)(1+S)-1`. As `1+S` is a positive integer, equality to zero forces `S=G=0`; the converse is immediate. The upper degrees are `deg S<=36`, `deg G<=44`. The degree-80 term has coefficient `-2^34 3^58 beta^50` at `h^6 w3^8 v^14 J3^50 t^2`, proving exactness. No claim that `1+G` is positive away from the zero set is needed.

## Validation and limits

After inspecting the execution surfaces, I ran only these local integer scripts in scratch copies, with the existing SymPy 1.14 environment:

- Shears: `integer/build.py` and `integer/check.py`, normal and `-O`.
- Radical residue: `integer/build.py`, `integer/circuit.py`, `integer/verify.py`, and `integer/independent_review.py`, normal and `-O`.

All twelve stages returned zero. All five shears forms and ten radical forms regenerated byte-for-byte identically; normal and optimized script output hashes also agree. There was no Lean, TeX, pip, network operation, or execution of the positive/nine/release components. The scratch receipt is `/tmp/proofs62ff-radical-shears-integer-replay/REPLAY.json` and is embedded in the committed review receipt.

The new independent tool `tools/review_radical_residue_shears_integer.py` imports no package builder. It authenticates both intake archives, all stored source pins, the whole matching tuple, literal degree upper/lower checks, actual DAG topology/liveness/counts, and exact short symbolic identities for the norm shifts, scaled resultant, midpoint, and degree-110 shear. It also checks 35,301 bounded midpoint/parity controls. It passes normally and under `-O`; neither mode depends on Python `assert` statements. The companion JSON files record hashes and exact results.

The finite algebra/circuit checks certify transcription, degree, and implementation claims. The unbounded integrality proof above and the inherited source/native calibration are separate logical obligations. These packages give ordinary reductions formalizable in ZFC; this review does not relabel that as a completed Lean proof of the final internal-ZFC equivalence.
