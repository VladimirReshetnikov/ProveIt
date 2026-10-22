# Exact fixed coefficients for the K215 Diophantine instance

This file fixes every constant of the proposed polynomial. The constants are
ordinary positive or nonnegative integers, independent of all Diophantine
witnesses. Their definition uses only a bounded finite enumeration and integer
arithmetic. No unspecified universal index, halting oracle, consistency oracle,
or choice of an r.e.-set representative occurs.

The coefficients are extraordinarily large. The full K215 window alphabet and
the decimal or binary expansions of these numerals have **not** been
materialized. `fixed_compiler.py` is an executable standalone port of the
published finite recipe; `fixed_constants.json` records its exact specialization
and compact symbolic definitions. Finite definitions of integer coefficients
are separate from variable exponentiation: every exponent below is a fixed
integer and the resulting equation is an ordinary polynomial.

## 1. Source and exact ordered windows

The source snapshot is
`cdd582bec13f908df3711fa9e05d1ddac368a5db` of
`VladimirReshetnikov/ProveIt`. The exact binary machine table is `k215.tm`,
SHA-256
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.

Use the exact `NormalizedK215` machine and tile IDs defined in
`normalized_k215.py`; see `normalization.md` for its all-time simulation proof.
The tile alphabet size is

\[
a=3502.
\]

Let \(w_0\) be its distinguished Start window, \(w_1\) its End window,
and list every other locally allowed 9-tuple in lexicographic order of the
tile IDs. Each local test reads only the center and its four cross neighbors.
The four corner coordinates are unrestricted. The exact independently checked
cross count and total are

\[
C=136449173881235,\qquad
k=C\,3502^4=20522746353535702537070419760.
\]

The count is derived in `normalization.md` and implemented by
`count_allowed_windows`. The count formula has also been compared with brute
enumeration on two small machines. It does not enumerate the actual K215 list.
The deterministic iterator `iter_allowed_windows()` specifies every \(w_i\).
Its straightforward implementation visits at most \(3502^9\) candidate tuples;
this is a fixed finite number, with no computation-history bound to discover.

## 2. Exact layout parameters

The selector/clause radix is \(A=2^{95}\). Define

\[
\begin{split}
p&=(k-73736)/2=10261373176767851268535173012,\\
J_\mu&=31522+p=10261373176767851268535204534,\\
\mu&=A-2+\sum_{j=1}^{J_\mu}A^j,\\
M&=k+15a+1=k+52531=20522746353535702537070472291.
\end{split}
\]

There is exactly one ignored native dummy position. For
\(r,c\in\{0,1,2\}\) and \(0\le s<a\), put

\[
e(r,c,s)=k+3a+(2-r)3a+(2-c)a+s,
\qquad e_* = k+12a.
\]

The native positions are

\[
E=\{0,\ldots,k-1\}
\cup\{k+3a,\ldots,k+12a\}
\cup\{M,3M,9M,27M\}.
\]

The final member of the middle interval is the dummy. Define

\[
\begin{split}
H&=51M+3a+1,\\
T_1&=105M+4a+2,\\
T_2&=159M+4a+3,\\
g&=186M+4a+4.
\end{split}
\]

The remaining fixed lengths and bases simplify exactly to

\[
\boxed{L=5^{44},\quad b=5^{43},\quad d=bL=5^{87},
\quad R=2^b,\quad B=2^d.}
\]

These simplifications follow from the literal compiler's least-power-of-five
choices, not from an arbitrary increase of the coefficient size. Specifically,

\[
5^{43}<213M+4a+5\le5^{44},\qquad
5^{42}<95J_\mu+2\le5^{43}.
\]

For the second inequality, the padded mask dominates the radix-size bound.
Let \(S_c\) be the sum of the nonzero native clause coefficients defined below
and \(K=|E|=k+31523\). The coefficients of selectors, copies, and anchors give
\(S_c<2A^{31523}\), while \(K+2<A\). Thus the mass term
\(4(K+2)(2S_c+6)+8\) is less than \(A^{31525}\), whereas
\(2\mu+4\) is larger than \(2A^{31522+p}\), with \(p>3\).
Consequently the literal maximum is \(2\mu+4\). Since
\(A^{J_\mu}\le\mu<2A^{J_\mu}\) and \(A\ge4\), more precisely
\(\mu<\tfrac43 A^{J_\mu}\), the bit length of \(2\mu+3\) is
\(95J_\mu+2\). This is exactly the compiler's required radix bit length
before taking the least power of five.

## 3. Native clause coefficients and transport constants

For selector \(0\le i<k\), define

\[
c_i=1+\sum_{r,c=0}^{2} A^{1+(3r+c)a+(w_i)_{3r+c}}
       +\sum_{t=0}^{3}A^{1+9a+t}.
\]

For copy positions and the four anchors, define

\[
c_{e(r,c,s)}=A^{1+(3r+c)a+s},\qquad
c_{\lambda_t M}=A^{1+9a+t},\quad
(\lambda_0,\lambda_1,\lambda_2,\lambda_3)=(1,3,9,27).
\]

The ignored dummy has coefficient zero. These definitions specify the entire
finite coefficient map. Put

\[
\begin{split}
D_C^0={}&R^{3a}+R^{H+a}+R^{8M}+R^{24M}\\
 &+\sum_{e\in E\setminus\{e_*\}}
       c_e\bigl(R^{T_1-e}+R^{T_2-e}\bigr),\\
D_R={}&R^H,\\
\epsilon={}&\begin{cases}
1,&5\mid 2D_C^0-D_R,\\
0,&5\nmid 2D_C^0-D_R,
\end{cases}\\
D_C={}&D_C^0+\epsilon R^g,\qquad
K_0=D_C+BD_R.
\end{split}
\]

All exponents here are positive, and their support lies below \(L\).
The one fixed Boolean \(\epsilon\) is determined by this finite integer
expression; it is **not a polynomial witness**. It may equivalently be
computed by substituting \(R=2\pmod5\) in the finite sum. The correction
ensures \(2D_C-D_R\not\equiv0\pmod5\). No computation of the K215 run is
part of this decision.

## 4. Masks, aliases, and the fixed marker

The native low mask and high mask are

\[
\begin{split}
M_C={}&B-1-\sum_{e\in E\setminus\{1\}}R^e-2R^{e_*},\\
M_F^{\rm nat}={}&4+\mu(R^{T_1}+R^{T_2})\\
 &+\sum_{\substack{r=0,1\\c=0,1,2\\0\le s<a}}R^{e(r,c,s)}
  +\sum_{\substack{r=0,1,2\\c=0,1\\0\le s<a}}R^{H+e(r,c,s)}
  +R^{9M}+R^{27M}.
\end{split}
\]

The compiler's theorem applies to these exact masks. In particular,
\(0<M_C,M_F^{\rm nat}<B-1\), \(M_C\equiv2\pmod4\),
\(M_F^{\rm nat}\equiv4\pmod8\), and their binary populations sum to \(d\).
The shifted fixed coefficient used by the polynomial is

\[
M_F=M_F^{\rm nat}+B-1.
\]

The source name `MF` means this shifted coefficient; the native-mask range
must never be imposed on it. The other source aliases are `Bm1` \(=B-1\),
`Kconstant` \(=K_0\), `inner_bits` \(=b\), and `twice_cell_bits` \(=2d\).
The fixed-input specialization sets raw \(x=1\), hence fixes End at cell 2
and uses the numerical marker

\[
\boxed{W_0=R B^2=2^{5^{43}+2\cdot5^{87}}.}
\]

The normalized machine erases its four-one input and simulates blank K215.
Therefore this fixed marker retains exactly the requested halting predicate.

## 5. What has actually been computed

The normalized transition table, local predicate, exact window count, and
the layout parameters above have been evaluated and checked. The standalone
compiler was compared field by field with the two inspected parent compiler
functions on five finite fixtures, including both values of the optional
correction. On the smallest fixture all full fixed numerals were materialized,
the native mask ranges/populations were checked, and six exact modular
evaluations agreed. `fixed_compiler_checks.json` records those results.

For the actual K215 instance, \(B\) alone has \(5^{87}+1\) binary digits,
approximately \(6.46\times10^{60}\) bits. The proposed simplification targets
the number of variables, polynomial degree, and arithmetic instructions;
it does not provide small coefficient bit length. `Kconstant`, `MC`, and
`MF` retain the exact bounded finite definitions above. The full tuple of
giant expanded numerals has not been computed, and no new proof-assistant
verification of the helical compiler is claimed.

## 6. Upstream proof references

All paths are below `Computability/HilbertTenthProblem` at the pinned snapshot.

- `Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md`: complete arithmetic theorem.
- `Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md`:
  modified masks, enlarged radix bound, spill case, and fixed export convention.
- `Papers/verification/explore_fixed_raw_universal_76.py`: base finite layout.
- `Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.py`:
  exact modified compiler.
- `Papers/1980/FIXED_RAW_UNIVERSAL_81_PROOF.md` and
  `Papers/1980/EXPLORATION_HELICAL_UNARY_TABLEAU.md`: stationary Start/End
  normalization and finite marked-computation semantics.
