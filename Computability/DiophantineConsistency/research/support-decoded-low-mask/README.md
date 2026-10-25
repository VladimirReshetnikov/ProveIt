# Recover the low mask from the already printed coefficient polynomial

The accepted indexed943 constant recipe contains a redundant support-set
definition. The exact same low mask can instead be recovered from the
already printed polynomial Phi and base-digit function D_b. This removes
the entire union-of-intervals E definition while preserving every one of
the four fixed integers. It introduces no machine, tuple, controller,
polynomial or calibration change. The proposed recipe is complete below.

This is a code-free ordinary identity and an inert full-text comparison.
No application was imported, compiled or run; no tuple was generated;
no TeX/PDF utility ran; no candidate or maintained page was changed.
The printed-character comparison below is a charged extraction proxy,
not a claim that a new rendered page or measured page improvement exists.

## 1. Exact identity and coefficient support

Retain the complete current indexed943 recipe, rho=2^67 and beta=B-1.
Write its already printed fixed polynomial as

    Phi(x)=sum_(e=0)^3296 c_e*x^e.

For the943 selector positions0..942,

    c_e=1+2^51-2^10*v(t_e),
    v(w,n,e,s)=w+2^8*n+2^17*e+2^25*s+127*2^34.

All actual labels obey0<=w,e<2^8 and0<=n,s<2^9. Therefore

    127*2^34 <= v(t) < 128*2^34=2^41,
    1 <= c_e <= 1+2^44 < 2^45 < rho.

The remaining41 nonzero coefficients are specified by the complete
printed11-triple C table: each triple(b,e,m) gives coefficients
2^(b+j) at positions e+j for0<=j<m. The four intervals have lengths
8,9,8,9 and there are seven singletons. Their supports are pairwise
disjoint and disjoint from0..942; all coefficients are at most2^50<rho.
These are exactly

    {983,...,992} union {1003,...,1011}
      union {1013,...,1031} union {1095,2195,3296}.

Hence every coefficient is in0..rho-1, and the nonzero support is exactly
E\{1063,1064}. The two omitted positions are the old zero-coefficient
dummy slots. This uses the actual complete selector/control recipe,
not a nonzero-coefficient assumption about an arbitrary polynomial.

For the existing function

    D_b(A,k)=floor(A/b^k) mod b,

the usual carry-free positional identity gives

    D_rho(Phi(rho),e)=c_e, 0<=e<=3296.

For any integer d in0..rho-1,

    floor((d+rho-1)/rho) = 0 if d=0, and1 otherwise.

Consequently, with only fixed finite indices,

    U=sum_(e=0)^3296
        floor((D_rho(Phi(rho),e)+rho-1)/rho)*rho^e
      =sum_(e in E\{1063,1064}) rho^e.

The old low-mask formula is

    MC=beta-sum_(e in E\{1}) rho^e-2*rho^1063.

Selector1 is nonzero, while both dummy coefficients vanish. Thus

    sum_(e in E\{1}) rho^e
       =U-rho+rho^1063+rho^1064,

which proves the proposed single replacement

    MC=beta+rho-(rho+3)*rho^1063
       -sum_(e=0)^3296
          floor((D_rho(Phi(rho),e)+rho-1)/rho)*rho^e.       (1)

The temporary U is only used in this proof; it is not added to the page.
The full proposed body below inlines the indicator and adds no notation.

## 2. Whole tuple and complete finite specification

All definitions other than MC and the now-unused E paragraph stay byte
identical. In particular beta,K,MF_source,Phi,the943 indexed tiles,
436-character seed, alphabet and430-action decoder are unchanged. Equation
(1) proves equality of MC as an integer. Therefore the entire four-port
tuple, including all295388 canonical raw bytes, has exactly the accepted
value; there is no isolated K substitution or new native/controller
premise. The arithmetic66-gate polynomial, positive domain and ordinary
unsolvability/Con(ZFC) equivalence consequently remain identical.

The reference to D_rho and Phi before their displayed definitions is
acyclic. D_b is a universally defined arithmetic function of its three
arguments, not a routine reading the seed. The seed and D_b define the
actions, the actions define the finite tiles, the tiles define Phi, and
only then is (1) evaluated. No coefficient table, external program,
variable search or machine execution is hidden in this dependency graph.
Every sum is fixed and finite, and all quotients/remainders are applied
only in fixed-constant definitions as permitted by the task.

This is a same-tuple display rewrite. It does not prove a new compiler
theorem, formalize the existing one or resume Lean. The accepted whole
indexed/native/Pell/K215-refutation proof remains the semantic boundary.

## 3. Charged complete-body comparison and its limits

The full proposed constant body in section5 is derived from the exact
accepted fifteen66 body, starting at the fixed-integers marker and ending
at end{document}, by precisely two changes: delete the entire Define/E/
Then paragraph and replace its MC line by (1). Both formula lines and
all other body bytes, including every seed/alphabet character and footer,
are charged. The new formula is split across two alignment lines; there
is no new indicator-function heading or abbreviated external definition.

| Complete-body source metric | Accepted | Proposed | Saving |
|---|---:|---:|---:|
| UTF-8 bytes, including fixed-integers marker |4099|3978|121|
| Nonwhite source characters, same scope |3813|3701|112|

The accepted entire extracted constant-and-footer suffix has2553 nonwhite
characters. Its exact old Define/E/Then/MC segment has122. Replacing just
that segment by the complete visible mathematical character stream

    MC=beta+rho-(rho+3)rho1063-Sum3296e=0floor((Drho(Phi(rho),e)+rho-1)/rho)rho^e,

where beta,rho,Phi,Sum and each floor delimiter are charged as their actual
single mathematical glyphs, gives49 replacement characters and a2480
character full-suffix proxy, saving73. The exact charged Unicode stream
is stored in SOURCE_PINS.json. Every bound, arithmetic sign, parenthesis,
comma, sub/superscript digit and both floor delimiters is included.
Existing D_b, its full quotient/remainder definition, the complete
alphabet, positional sum and entire seed remain in both full suffixes.

Keeping every other existing extracted glyph identical gives a proposed
whole-page proxy3025-73=2952, and a recipe proxy2343-73=2270. These are
not new PDF measurements. Actual layout, line breaking, glyph extraction,
font/readability and page count require a separately reviewed page
preparation, actual-TeX/whole-tuple audits, typesetting, corruption controls,
pure rerenders and independent visual checks. No page is promoted here.

The source metric is exact for the two complete text bodies. The visible
metric is explicitly a proxy made by editing the whole accepted PDF text,
not by mistaking TeX commands for printed characters. It charges all new
notation but cannot certify how a new typesetter run would extract it.
The potential gain is modest, and nested digit/floor notation may make
this recipe less convenient to read even though it removes a support set.

## 4. Prior work and the smaller-radix boundary

SEED_COMPRESSION54.md and SEED_PREDICTORS54.md already charge decoder,
alphabet and positional-sum overhead; their rejected affine predictors,
DFS/discovery alternatives, extra exception masks and variable-width
targets do not supply a free seed saving. They also cover merging seed
masks and collecting selector coefficients. The current indexed proof
already removes selector sorting by a direct943-tile enumeration. I found
no support-from-Phi low-mask identity in those inspected notes. This is a
bounded search of the named sources, not a claim about all Git history.
The closed mixed-radix-bfs-seed proof gives a further concrete warning:
its generic/fixed-halt recipes save37--39 seed characters but pay64--72
decoder characters, leaving the complete recipes26--35 characters longer.
Those are comparisons of those specific accepted formulations, not a
lower bound against every other mixed-radix decoder.

Merely changing rho to a smaller power of two would change the whole
tuple and its controller. The retained sufficient carry threshold is
118788496120850159560; it exceeds2^66=73786976294838206464 and is below
2^67=147573952589676412928. Thus67 is the smallest bit width satisfying
that exact retained bound. A sharper coefficient bound or new geometry
may be possible, but would need its own whole native/controller proof.
No smaller-radix tuple or calibration is supplied here. Formula(1) avoids
that obligation by leaving every fixed integer unchanged.

## 5. Entire proposed constant body, as inert mathematical text

This is the full replacement body, not an emitted standalone TeX file or
an executed page. It retains the original marker and footer verbatim.

```tex
\textbf{The four fixed integers.}
Every index, set, sum, product and floor below defines a constant, not
another unknown. Put
\[
\rho=2^{67},\quad B=\rho^{8807},\quad\beta=B-1,\quad
G_m(x)=\sum_{j=0}^{m-1}x^j.
\]
\begin{align*}
M_C={}&\beta+\rho-(\rho+3)\rho^{1063}\\
&-\sum_{e=0}^{3296}\fl{(D_\rho(\Phi(\rho),e)+\rho-1)/\rho}\rho^e,\\
M_F={}&B-1+4+(2^{51}-2)(\rho^{4393}+\rho^{5495})\\
&+\rho^{1013}G_{10}(\rho)+\rho^{1065}G_9(\rho)
  +\rho^{2195}+\rho^{3296}\\
&+(2^{65}-1)\rho^{8792}G_{13}(\rho)+(2^{19}-1)\rho^{8805},\\
K={}&\rho^{30}+\rho^{62}+\rho^{1100}+\rho^{2201}+\rho^{8849}\\
&+(\rho^{4393}+\rho^{5495})\Phi(1/\rho),
\end{align*}
where
\[
\begin{split}
\Phi(x)={}&(1+2^{51})G_{943}(x)
 -2^{10}\sum_{i=0}^{942}v(t_i)x^i\\
&+\sum_{(b,e,m)\in\mathcal C}2^b x^e G_m(2x),\\
\mathcal C={}&\{(10,1023,8),(18,1013,9),(27,1003,8),\\
&(35,983,9),(44,1031,1),(45,1022,1),(46,1011,1),\\
&(47,992,1),(48,1095,1),(49,2195,1),(50,3296,1)\}.
\end{split}
\]
The rational intermediate in K cancels exactly; all four results are positive integers.

\textbf{The 943 indexed fixed tiles.}
Use the actions $u_j,v_j,d_j$ decoded below. Let
\[
\begin{gathered}
h(q,b)=2(q+1)+b,\quad
\mathcal R=\{u_j:d_j=1,\ 0\le j<430\},\\
\mathcal L=\{u_j:d_j=0,\ 0\le j<430\},\\
r_q=6+|\mathcal R\cap\rg0{q-1}|,\quad
l_q=205+|\mathcal L\cap\rg0{q-1}|.
\end{gathered}
\]
An interval ending at $-1$ is empty. The table defines $t_i$ for
$0\le i\le942$; all index ranges are fixed:
\[
\setlength{\arraycolsep}{1.4pt}\begin{array}{c|l}
\text{index }i&\text{tile }t_i=(w,n,e,s)\\\hline
0,1&(2,435,3,1),\ (5,0,0,0)\\
j+2\ (j=2q+b<430)&((1-d_j)l_{u_j},h(q,b),d_jr_{u_j},v_j)\\
432+b\ (b=0,1)&(0,h(215,b),0,h(215,b))\\
434+b\ (b=0,1)&(0,b,0,b)\\
424+2r_q+b\ (q\in\mathcal R,b=0,1)&(r_q,b,0,h(q,b))\\
424+2l_q+b\ (q\in\mathcal L,b=0,1)&(0,b,l_q,h(q,b))\\
924+j\ (0\le j<4)&(0,j+430\fl{j/2},0,438)\\
928&(2,434,2,0)\\
929&(3,436,4,4)\\
930&(4,436,4,0)\\
497+t\ (t=434,435,436)&(1,438,1,t)\\
\substack{934+3a+b-6\fl{a/4}\\a\in\{0,1,4\},\ b=0,1,2}&(a,437,b,437)
\end{array}
\]
For $t=(w,n,e,s)$ put
\[
v(t)=w+2^8n+2^{17}e+2^{25}s+127\,2^{34}.
\]

\textbf{A closed decoder for the 430 actions.}
Put $D_b(A,k)=\fl{A/b^k}\bmod b$, where
$a\bmod b=a-b\fl{a/b}$. For $0\le q<215$, $b=0,1$, $j=2q+b$:
\[
\begin{gathered}
N=\mathcal A\bmod2^{636},\quad
T_0=\fl{\mathcal A/2^{636}}\bmod2^{1675},\\
E_0=\fl{\mathcal A/2^{2311}},\\
\nu_j=D_2(N,j),\quad \sigma_j=\sum_{k=0}^{j-1}\nu_k,\\
m_q=D_2(N,430+q),\quad \tau_q=\sum_{k=0}^{q-1}m_k,\\
F_q=14(1-m_q)+m_qD_{16}(E_0,\tau_q),\\
u_j=\nu_j(1+\sigma_j)+(1-\nu_j)D_{216}(T_0,j-\sigma_j),\\
v_j=D_2(F_q,2b),\quad d_j=D_2(F_q,2b+1).
\end{gathered}
\]
Empty sums are zero. Here $(v_0,d_0,u_0)=(1,1,1)$; the constructor tile
uses this actual first target, including its state renaming.

\textbf{The integer $\mathcal A$.}
The alphabet, in order of digit values $0,\ldots,61$, is
{\fontsize{7.7}{8.2}\selectfont\ttfamily 0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz}.\par
Concatenate the following 436 characters as digits $e_0,\ldots,e_{435}$;
put $\mathcal A=\sum_{j=0}^{435}e_j62^{435-j}$.\par
\begingroup\fontsize{7.7}{8.2}\selectfont\ttfamily
BxEnhvy6NipzkWmROo0GsA3uK3twWLxscLq20UTumy5Cdu461LwD6g7RDNzF8Y\par
iYDFTpB8ehAypd7d6OsOL4APamnJeNXQypUezCmW9n4oXP6XfgmiWuAWZ8ZJ7U\par
OP7gu4kVdlGZqZHULQMar1dXNeJW4i7oNVI8usp8BlovjjZbwPCovZI328fRUq\par
4q92R81s5GjWQaQfGhkq9UYMK3rRMaBmsOIBkJqc2cj2VRIZ6mjzkBIOkW9SjZ\par
FzeA6J5u4j3sBL3SdgwXzM9mHvQivu8EJ1TBTpRhHDqZIbmYgwQ8VqTAFotl6F\par
We1YC554GKrVHsA8oUGKSA6F6k5KREBSD0Tgd7bFALY84LLbpw574BQyvdoHrl\par
0Oe35uwDf15DpT6VJWZBjSbHPpPAINYTte0eUxnTFTKBlGj8Am6sb1gLldh8WZ\par
8P\par
\endgroup
\normalfont\fontsize{7.7}{8.2}\selectfont
The ordinary state/color-conjugacy, native and Pell arguments give
unsolvability iff $\mathrm{Con}(\mathrm{ZFC})$.
Native calibration and internal-ZFC formalization remain open in Lean.
This page is a complete finite specification, not an unsolvability proof.
\end{multicols}
\end{document}
```
