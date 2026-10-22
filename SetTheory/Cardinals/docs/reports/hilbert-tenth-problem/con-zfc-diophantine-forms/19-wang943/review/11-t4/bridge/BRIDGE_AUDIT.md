# Audit and smaller coefficient backend for the combined consistency equation

## Result

The raw blank-input K215 backend of report 06 is compatible with report 08's 34-positive-variable quartic lift. The 08 lift is algebraic and uses only the same six equations and their positive-extension facts. It does not require the larger input-erasing machine, 4,366-symbol cell alphabet, global uniqueness of Start, an End selector, or a rectangular divisibility condition on the arithmetic stride. Therefore the **literal 06 four coefficients**, not 08's coefficients, may be used in the 08 quartic unchanged.

A further adapter proved here replaces 06's 3-by-3 window alphabet by a four-cell T-shaped alphabet, adds one harmless local one-head restriction, and moves initialization recognition onto the outgoing temporal edge. This produces **37,075 tiles**, explicitly materialized, and changes the fixed coefficients to a new fully specified four-tuple. The same polynomial and quadratic/quartic algebra then applies, with

\[
B=2^{5^{18}}=2^{3\,814\,697\,265\,625},
\]

rather than 06's \(2^{5^{67}}\). This is a coefficient-description/height improvement, not a variable/degree improvement by itself. The numerals remain enormous and are not expanded.

The new adapter is an ordinary mathematical proof using the repository's proved native compiler/Pell results and exact K215 endpoint. The finite checks below establish their explicitly limited finite claims. No fresh complete Lean/Rocq build, internally encoded ZFC derivation, or proof of Con(ZFC) is claimed.

## Source pins

All current repository links in this audit are pinned to `3b201cdea32d2c816f5f3d20734051f25fd3ef14`. The reports themselves describe their inherited mathematical sources at `cdd582bec13f908df3711fa9e05d1ddac368a5db`; these two roles must not be conflated.

- [06 report](https://github.com/VladimirReshetnikov/ProveIt/blob/3b201cdea32d2c816f5f3d20734051f25fd3ef14/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/06-blank67/report.tex)
- [06 exact local predicate](https://github.com/VladimirReshetnikov/ProveIt/blob/3b201cdea32d2c816f5f3d20734051f25fd3ef14/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/06-blank67/code/blank_helical.py)
- [06 coefficient recipe](https://github.com/VladimirReshetnikov/ProveIt/blob/3b201cdea32d2c816f5f3d20734051f25fd3ef14/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/06-blank67/code/compiler_constants.py)
- [06 helical proof](https://github.com/VladimirReshetnikov/ProveIt/blob/3b201cdea32d2c816f5f3d20734051f25fd3ef14/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/06-blank67/proofs/blank_helical_proof.md)
- [06 imported theorem ledger](https://github.com/VladimirReshetnikov/ProveIt/blob/3b201cdea32d2c816f5f3d20734051f25fd3ef14/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/06-blank67/data/proof_dependencies.json)
- [08 quartic and inputless system](https://github.com/VladimirReshetnikov/ProveIt/blob/3b201cdea32d2c816f5f3d20734051f25fd3ef14/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/08-start-only67/diophantine_zfc.tex)
- [Literal transition data](https://github.com/VladimirReshetnikov/ProveIt/blob/3b201cdea32d2c816f5f3d20734051f25fd3ef14/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/06-blank67/data/k215_transitions.json)
- [Unconditional Lean endpoint](https://github.com/VladimirReshetnikov/ProveIt/blob/3b201cdea32d2c816f5f3d20734051f25fd3ef14/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean)
- [Ordinary K215 calibration proof](https://github.com/VladimirReshetnikov/ProveIt/blob/3b201cdea32d2c816f5f3d20734051f25fd3ef14/Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md)
- [ZF/ZFC proof transport](https://github.com/VladimirReshetnikov/ProveIt/blob/3b201cdea32d2c816f5f3d20734051f25fd3ef14/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean)

Downloaded Python files in `sources/` were read as source, not imported or executed. The two `check_*.py` programs here are newly authored independent checks and read only the literal transition JSON as input.

## 1. Original 06 bridge audit

### 1.1 Correct machine and halting convention

Keep all 430 K215 actions exactly as exported. State 0 is initial, tape symbol 0 is blank, working states are 0 through 214, and 215 is halt. In particular the real first action is \((0,0)\mapsto(1,+1,93)\), and the transition entering halt retains its write and movement. Only after entering state 215 is the completion \((215,b)\mapsto(b,0,215)\) used for padding. Thus the padding completion does not change whether the original machine halts.

The dense table is bound in the source package to SHA-256 `fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`. The new checks read its literal 430-action JSON projection, whose source-binding claims are kept separate from the universal endpoint theorem.

### 1.2 Arbitrary stride is sound

For a cyclic word of length \(N\), the 06 overlaps imply that the window entry at displacement \((x,t)\) is the center symbol at index \(i-x-ht\pmod N\). This follows by overlap identities, even if some of these residues coincide. Pullback along \((x,t)\mapsto-x-ht\pmod N\) therefore yields a globally valid plane with periods \((N,0)\) and \((0,N)\). Neither \(h\mid N\) nor \(\gcd(h,N)=1\) is needed. The distinguished Start excludes the zero temporal shift.

### 1.3 No global unique-Start assumption

The initialized phase graph is \(L\to L,Q\), \(Q\to R\), \(R\to R\). It has no cycle through Q. Horizontal periodicity around the marked Q therefore supplies vertical boundaries on both sides. Choose the nearest two. Propagating boundaries forms a finite strip. The horizontal boundary before Q propagates across that strip; temporal periodicity supplies a next horizontal boundary. Between them the first row is exactly \(L^uQR^v\), with \(u,v\ge1\). The local deterministic updates and no-escape rule preserve its one head. Its last interior row is halted. Other strips, other Start occurrences, and unrelated periodic components do not affect this argument.

### 1.4 Forbidden locally valid window is harmless

06's special selector-1 window is center-valid but globally impossible because its prior H has vertical bit 0 and its current V has vertical bit 1. The prior center's propagation rule contradicts this in every extension. Forbidding selector 1 therefore removes no computation. The 08 historical End selector must not be retained when changing to these coefficients.

There are orientation slips in the 06 standalone prose (it sometimes says above/below in the opposite orientation). The executable predicate and report use time increasing from prior to following; under that convention the last interior head is immediately **before** H and must halt. The orientation slips do not affect the precise predicate or the proof when consistently read in this convention.

### 1.5 Completeness and tuning

A finite halt admits arbitrary sufficiently large independent width and height by blank margins and absorbing halt padding. The helical extension

\[
T(x,t)=G(x\bmod w,(t+\lfloor x/w\rfloor)\bmod H)
\]

is valid at every seam because V is time-independent, carries no payload, is blank/headless to updates, and stops horizontal boundary propagation. Its periods \((w,-1),(0,H)\) give a cyclic presentation of length \(wH\) with exactly one canonical Start. Uniqueness is used only for this chosen completeness witness and the special origin mask, never for soundness.

The actual packed-index adjustment uses free dummy bits, not an independently chosen formal exponent. Its coefficient is a unit modulo the relevant power of five because \(2D_C-D_R\equiv3\pmod5\). This part of the 06 adapter remains valid for the new coefficients below.

## 2. New four-cell local language

### 2.1 Cells

Use the same 439 cell symbols:

- ordinary headless symbol \(b\in\{0,1\}\) has code \(b\);
- ordinary symbol b with head state q has code \(2(q+1)+b\), for \(0\le q\le215\);
- \(L=434,Q=435,R=436,V=437,H=438\).

The phases L,Q,R have payloads \((0,\varnothing),(0,0),(0,\varnothing)\). V and H are payloadless; V has vertical bit 1, H has horizontal bit 1, and ordinary/phase cells have both bits zero.

A tile is now a tuple \((l,c,r,n)\): left, center, right, next-time center. Its exact predicate is `valid` in `check_t4.py`. Equivalently:

1. At most one of l,c,r has a head (Q counts as a head).
2. c is V iff n is V. c and r are not both V. c and n are not both H.
3. If neither c nor r is V, they agree on whether they are H.
4. If c is V, no further requirement is imposed.
5. If c is H, n is one of L,Q,R.
6. At an interior c with an initial phase, require L when l is V, R when r is V, and, unless r is V, require the phase edge in \(LL,LQ,QR,RR\).
7. An interior head cannot move into an adjacent V.
8. If n is H, c is headless or its head state is 215.
9. Otherwise n is an ordinary (nonphase) interior symbol, and is the exact deterministic three-neighbor successor of l,c,r. V is blank/headless; an H neighbor cannot supply this update. The successor tape bit is c's written/stable bit; incoming heads are determined by the completed transition table, and multiple arrivals are forbidden.

This replaces only the placement of the initialization test: it is now on the outgoing temporal edge rather than inspecting a fifth, prior-time cell.

### 2.2 Global equivalence of phase recognition

In a globally valid T4 plane, an interior cell has a phase iff the preceding cell in its column is H. Indeed its predecessor cannot be V, by vertical propagation; if the predecessor is H, rule 5 forces a phase; if the predecessor is interior, rule 9 forces no phase. Conversely the old global initialization rule implies exactly rules 5 and 9. The remaining centered transition/boundary clauses are unchanged. Thus, apart from the explicitly added one-head filter, global T4 validity is equivalent to the old five-cell-cross validity. No assumption about unique Start enters this reasoning.

### 2.3 Distinguished tiles

Put

\[
S=(434,435,436,1),\qquad E=(438,0,0,438).
\]

Both pass the exact finite predicate. S centers on initialized Q; its successor bit is forced by K215's actual first transition. E is locally valid because its headless center is immediately before H, so its malformed left neighbor is not used for an update. But E cannot occur globally: its left H has non-V right neighbor 0, contradicting rule 3 at that left cell. Therefore forbidding E is harmless, independently of the run.

Enumerate S first, E second, and all other passing tuples lexicographically in order (left,center,right,next). This is a bounded, terminating coefficient definition and does not run K215 to determine whether it halts.

### 2.4 Exact count

Independent direct enumeration exhausts all 46,980 horizontal triples satisfying the head filter, paired with all 439 successors: 20,624,220 quadruples. Exactly 37,075 pass. A second class-factorized counter gives the same number:

- ordinary headless bit 0: 9,148;
- ordinary headless bit 1: 9,148;
- 430 working-head symbols: 20 successors/neighborhoods per symbol, total 8,600;
- two halt-head symbols: 55 per symbol, total 110;
- L: 888; Q: 4; R: 1,750;
- V: 4,793; H: 2,634.

Here there are 433 headed symbols (432 ordinary plus Q) and six headless symbols (0,1,L,R,V,H). For a headless ordinary center, the next-H cases number
\(6\cdot5+433\cdot5+6\cdot433=4793\), and the ordinary-successor cases number \(5^2+2\cdot433\cdot5=4355\), totaling 9148. A working-head center has only ordinary successors and 5-by-5 headless neighbors minus the forbidden movement-side V, giving 20. A halt-head center has 30 next-H and 25 ordinary cases. For L, the two allowed right phases L,Q give 445 next-H and 443 ordinary cases. For Q, right is R and left has four allowed headless choices. For R, right is R or V and left cannot V, giving 876 next-H and 874 ordinary cases. For V, the same head-filter pair census is 4793, with unique successor V. For H, right is H or V and next has three phases, giving \(439\cdot2\cdot3=2634\). Thus the count is also an elementary closed finite calculation, independent of the enumeration program.

The complete ordered list is `t4_windows.json`, SHA-256 `9c2e473b5dbc5b3dc1468a31aefdbec6a901d6ba1e6b1ec9212698d41e1d84b1`. See `t4_verification.json` and `cross_count_receipt.json`. The list is small enough to materialize; the final coefficient numerals are not.

### 2.5 Overlap and arbitrary cyclic stride

For a tile w at i, its right neighbor at i−1, and next-time neighbor at i−h, impose only

\[
w_i(r)=w_{i-1}(c),\quad w_i(c)=w_{i-1}(l),\quad
w_i(n)=w_{i-h}(c).
\]

Write \(a_i=w_i(c)\). These identities imply

\[
w_i=(a_{i+1},a_i,a_{i-1},a_{i-h}).
\]

Hence every tile is exactly the actual four-cell neighborhood of the pullback plane \(a_{-x-ht}\). This remains true for all residue collisions. Axis periods N exist with no divisibility/coprimality condition. If h=0 mod N, S would have next value equal to its center, contrary to 1≠435.

### 2.6 Marked periodic T4 iff blank halt

Soundness follows from the original finite-strip argument in Section 1, because outgoing initialization was proved globally equivalent. The added head filter cannot create a false computation.

For completeness, take a finite genuine halt and choose at least two head-free tape cells between every visited head position and each vertical boundary. This is always possible because the run visits finitely many positions. Pad the halted tail arbitrarily. Inside a strip every horizontal triple has at most one head. At a vertical-boundary seam, both adjacent edge cells are head-free even with the helical one-row time offset, so the head filter still holds. All other seam clauses are the same as 06. Width and height can still be chosen independently as sufficiently large powers of five. The canonical cyclic witness has one S and no E.

## 3. The four new fixed coefficients

The following numeric recipe is the recommended frozen version. It retains 06's anchor geometry and tightens only the clause-band separation: since Emax is odd, T2=T1+2Emax+4 remains greater than T1+2Emax and has the required separation 2 modulo 4. This permits cell length 5^10.

Put

\[
a_0=439,\quad k=37075,\quad A=2^{16}=65536,
\quad \rho=2^{390625},\quad B=\rho^{9765625}=2^{5^{18}}.
\]

For \(u=0,\ldots,438\), define the four copy positions

\[
e_l(u)=40587+u,\quad e_c(u)=40148+u,\quad
e_r(u)=39709+u,\quad e_n(u)=38831+u.
\]

Let \(\mathcal E\) consist of the selectors \(0,\ldots,37074\), these 1,756 copy positions, dummy position 42,343, and anchors

\[
43661,\quad130983,\quad392949,\quad1178847.
\]

Thus \(|\mathcal E|=38836\). Define

\[
\mu=A-2+\sum_{j=1}^{18743}A^j.
\]

For tile \(w_i=(l_i,c_i,r_i,n_i)\), use clause coefficients \(v_e\) (not to be confused with the cell codes):

\[
\begin{aligned}
v_i={}&1+A^{1+l_i}+A^{440+c_i}+A^{879+r_i}+A^{1318+n_i}
          +\sum_{t=1}^4A^{1756+t},\\
v_{e_l(u)}={}&A^{1+u},\quad v_{e_c(u)}=A^{440+u},\\
v_{e_r(u)}={}&A^{879+u},\quad v_{e_n(u)}=A^{1318+u},\\
v_{3^{t-1}43661}={}&A^{1756+t}\quad(1\le t\le4),\qquad v_{42343}=0.
\end{aligned}
\]

Now set

\[
\begin{aligned}
D_C={}&\rho^{1317}+\rho^{2228468}+\rho^{349288}+\rho^{1047864}\\
 &+\sum_{e\in\mathcal E}v_e
   (\rho^{4586163-e}+\rho^{6943861-e}),\\
D_R={}&\rho^{2228029},\\
M_F^0={}&\mu(\rho^{4586163}+\rho^{6943861})
       +\sum_{u=0}^{438}\rho^{40148+u}\\
 &+\sum_{u=0}^{438}(\rho^{2228029+40587+u}+\rho^{2228029+40148+u})
       +\rho^{392949}+\rho^{1178847},\\
M_C={}&B-1-\sum_{\substack{e\in\mathcal E\\e\ne1}}\rho^e-2\rho^{42343},
\qquad M_F=M_F^0+4.
\end{aligned}
\]

The four polynomial ports are exactly

\[
\boxed{\beta=B-1,\qquad K=D_C+BD_R,\qquad M_C,\qquad M_F^*=M_F+B-1.}
\]

Do not replace \(M_F^*\) by the native mask \(M_F\), and do not combine any of these new coefficients with historical window orderings.

## 4. Compiler adapter proof

### 4.1 Layout and population census

The general five-cell/3-by-3 construction is used with only four copy slots and three copy-overlap groups. Write \(\ell=16,p=16983\), and

\[
m=2\ell+11a_0+8+2p=38835.
\]

There is one dummy because \(m+1-k-4a_0-4=1\). The population of μ is

\[
\operatorname{pc}(\mu)=\ell-1+18743=18758.
\]

There are three copy-overlap groups of a₀ bit positions each, and two tested anchor positions. Their fields do not overlap the two μ bands. Consequently

\[
\operatorname{pc}(M_F)=2\operatorname{pc}(\mu)+3a_0+2+1=m+1,
\qquad \operatorname{pc}(M_C)=d-m-1,
\]

where \(d=5^{18}\). Hence the population sum is exactly d, as required by the inverse-population lemma. Also

\[
0<M_C,M_F<B-1,\quad M_C\equiv2\pmod4,\quad M_F\equiv4\pmod8.
\]

The unused high positions make the inequalities strict. The extra factor 2 at the dummy removes its next binary bit from M_C, exactly as in 06.

### 4.2 Carry bound

Let npos=m+1 and

\[
U=4(\mathrm{npos}+2)(18(k+4a_0+4)+6)+8.
\]

Each selector coefficient has nine A-monomials counting its constant term; each copy/anchor coefficient has one. Therefore

\[
\sum v_e\le9(k+4a_0+4)A^{4a_0+4}.
\]

If \(M=(\mathrm{npos}+2)(2\sum v_e+6)\), then \(4M+8\le U A^{4a_0+4}\). The chosen radix satisfies

\[
b=390625\ge
\max\{16(18744)+3,\ 16(1760)+\operatorname{bitlength}(U)+1,\ 4\}
=299907.
\]

Thus \(\rho=2^b\) exceeds all original mass requirements, including \(4M+8\), \(2\mu+4\), and 16. The original no-carry estimates, including arbitrary bit rotations and the optional upper dummy bit, apply verbatim.

### 4.3 Exact field targets

Retain the original exponent grid \(e(r,c,u)=k+3a_0+(2-r)3a_0+(2-c)a_0+u\), but only at \((1,0),(1,1),(1,2),(2,1)\).

- The shift \(3a_0\) sends the next copy to the center copy. At center-copy mask positions the field tests current-next against temporal-neighbor-center.
- The shift \(H_C+a_0\), together with spatial transport \(D_R=\rho^{H_C}\), tests current-center against right-neighbor-left and current-right against right-neighbor-center.
- The shifts \(8M_0,24M_0\) test the two anchor pairs exactly as before.
- At the two clause bands, the contribution is exactly \(\sum v_e d_e\) from the native cell digits. The standard μ tests enforce either an empty cell or one selector, its four matching copies, and all four anchors.

Here \(M_0=43661,E_{max}=27M_0,H_C=51M_0+3a_0+1\). The exact set checks verify these 1,319 copy/anchor field targets for the actual support. Algebraically, all clause terms have exponent at least \(T_1-E_{max}\), above every copy/anchor target; the two clause bands are separated by \(2E_{max}+4\), so their contributions cannot interfere. The retained bare shifts hit only the indicated native positions. Removing unused corner/top slots cannot create a collision.

An occupied Start propagates occupancy through the horizontal neighbor tests, hence through the whole cyclic word because the spatial shift is one cell. The matching copies give precisely the three overlaps in Section 2.5.

### 4.4 All-rotation synchronization

The support is contained in \([0,E_{max}]\), with the possible extra spill position \(e_*+1\) also below Emax. The two clause-band rotation-hit sets are disjoint because their separation is \(2E_{max}+4>E_{max}\), and their opposite circular separation is greater than Emax. Thus at least one band is uncontaminated under every rotation.

Write a binary rotation exponent as \(bt+\epsilon\), \(0\le\epsilon<b\). The unshifted mass bound prevents carries. If \(1\le\epsilon\le b-2\), all rotated radix digits are even. If \(\epsilon=b-1\), only the single upper-dummy spill position can be odd. The marked cell's two anchor tests require two distinct odd rotated digits, excluding both cases. Therefore \(\epsilon=0\).

For an aligned radix rotation the two anchors require both 9M₀ and 27M₀ to lie in the shifted support. Their difference is 18M₀. The only support pair with that difference is (9M₀,27M₀): non-anchor support is below M₀; other anchor differences are not 18M₀; the cell circumference is far larger than all relevant differences. Hence the radix rotation is 0 modulo the cell length. This restores a whole-cell temporal rotation without imposing any extra arithmetic condition on its stride.

### 4.5 Five-adic unit and actual-rank tuning

The two clause-band terms cancel modulo 5 because \(b\) is an odd power of five, Emax=1,178,847 is odd, and \(T_2-T_1=2E_{max}+4\equiv2\pmod4\). Consequently

\[
D_C\equiv2^{3a_0}+2^{H_C+a_0}+2\pmod5.
\]

Since \(a_0=439\equiv3\pmod4\),

\[
\boxed{2D_C-D_R\equiv3\pmod5.}
\]

This is independent of the tile contents and of their ordering except the marked selector positions. The direct modular check over all 37,075 enumerated tiles gives the same value.

Choose sufficiently large powers of five w,H with H≥25 and N=wH>25d. Starting from the canonical word, turning on a free low dummy bit at cell j changes the **actual** packed rank by

\[
-\Gamma B^j,\qquad
\Gamma=\rho^{e_*}(q^2-1)[1+q(D_C+BD_R+B^w)],\quad q=B^N,
\]

provided j+1,j+w<N. Modulo 5 its bracket is \(2D_C-D_R\), so Γ is a unit modulo dN. The retained Boolean subset theorem on cells \(\{4j:0\le j<N/5\}\cup\{1\}\) gives an adjustment to the actual congruence \(R\equiv dw\pmod{dN}\). Width/height padding gives all its size and no-wrap hypotheses. No numerical input or End marker is involved.

The canonical origin high-mask test still holds: the field's unit radix digit comes only from a temporal-neighbor Start. There is one canonical Start and 0<w<N, so its temporal predecessor is not Start. Dummy changes occur at a positive, much higher native exponent and do not alter this test. Every dummy subset preserves the window choices and overlaps. The retained carry bound gives positive raw slack \(q-C-F\), and the rank/transport witnesses are completed exactly as in 06.

Thus every blank halt yields a positive solution, and every positive solution decodes a marked periodic T4 plane and hence a blank halt. The other arithmetic proof obligations are unchanged from the inputless six-equation system.

## 5. Exact ZFC calibration and trust boundary

The pinned Lean endpoint has the literal unconditional type

\[
\texttt{BlankHalts machine215}\ \leftrightarrow\
\texttt{BProv ZFCax_s [] Form.fBot}.
\]

There are no model-existence or consistency premises in its theorem statement. BProv means a finitary derivation from a finite list of axioms satisfying the indicated axiom predicate, not a fixed proof-length bound. ZFCax_s uses the ZF schemas plus a standard selector version of Choice; ordinary finite proof translations connect it with standard effective ZFC presentations.

The ZF/ZFC transport uses soundness/completeness and the internally constructed constructible class of an arbitrary model. It does not assume an externally well-founded, transitive, or omega-model. The ordinary calibration exposition explicitly concludes that the exact K215 halt/refutation equivalence is formalizable in ZFC. The imported compiler lemmas and this new finite local adapter use integer arithmetic, finite combinatorics, elementary induction and effective syntax, all formalizable in ZFC.

Accordingly the intended mathematical conclusion is unconditional:

\[
\mathrm{ZFC}\vdash
(\exists\text{ positive solution of the combined system})
\leftrightarrow\exists p\,\operatorname{Proof}_{\mathrm{ZFC}}(p,\bot),
\]

and its negation is equivalent to Con(ZFC). This conclusion relies on the repository's full universal compiler and endpoint proofs as imported mathematical theorems. Inspecting their statements, replaying finite table checks, or observing the successful finite enumeration is not an independent proof of those universal results. The new adapter has not been formalized in Lean/Rocq, and no internally encoded ZFC proof is supplied.

## 6. Comparison and exact size

The conservative intermediate reductions, all using the same raw K215 symbols, are:

| Local alphabet | Tile count | Base B |
|---|---:|---:|
| Original nine-cell 06 windows | 1,420,903,358,357,108,792,377 | \(2^{5^{67}}\) |
| Five-cell crosses, no new head filter | 38,256,607,897 | \(2^{5^{36}}\) |
| Five-cell crosses, one-head filter | 188,532,383 | \(2^{5^{30}}\) |
| Four-cell T, no head filter | 71,356,645 | \(2^{5^{28}}\) |
| **Four-cell T, one-head filter** | **37,075** | **\(2^{5^{18}}\)** |

Only the last is recommended as the main new coefficient recipe; the others provide transparent fallback comparisons. They are new coefficient choices, not re-interpretations of the literal old constants.

The fixed numeral β alone has exactly 3,814,697,265,625 bits, about 477 decimal gigabytes. K has exactly

\[
5^{18}+390625\cdot2228029+1
=4\,685\,021\,093\,751
\]

bits, about 586 decimal gigabytes. This follows from \(K=BD_R+D_C\), \(D_R\) a pure power of two, and \(0<D_C<B\). No final coefficient is expanded. The materialized tile list is under one megabyte and provides the finite content needed to determine every coefficient exactly.

## 7. Reproduction

Run only the newly authored programs:

```sh
python research_diophantine_combined/bridge/check_cross_counts.py
python research_diophantine_combined/bridge/check_t4.py
```

The first independently counts all four smaller alphabet variants by exhaustive local classes and computes scalar layouts. The second directly exhausts the filtered T4 candidates, writes the canonical alphabet, verifies all finite support/convolution/synchronization facts for the actual instance, checks the mod-5 unit, and checks two halting control machines across 927 local helical windows. It does not execute downloaded code, expand giant final numerals, or infer the unbounded K215 theorem from finite experiments.
