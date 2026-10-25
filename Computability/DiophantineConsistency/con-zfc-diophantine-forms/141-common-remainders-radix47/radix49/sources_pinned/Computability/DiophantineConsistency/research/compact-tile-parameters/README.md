# Compact the fixed tile parameters without changing a single coefficient

CODE-FREE ORDINARY PROPOSAL; independent review and actual rendering are pending.
This combines three elementary representation identities with the accepted grouped
recipe. It keeps the same indexed943 tile at each index, all430 actions,436 seed
characters, all four complete integers and the fifteen-positive66/157 polynomial.
No new application was imported, compiled or executed; no new tuple, source DAG,
standalone TeX, PDF, Lean theorem or main-page change was produced. The entire
proposed constant body is included below as inert text.

## 1. One rank family and one copy family

For fixed d=0,1 define

    S_d={u_j : d_j=d, 0<=j<430},
    r_(d,q)=205-199*d+|S_d intersect {0,...,q-1}|.

These definitions immediately give S_1=R, S_0=L, r_(1,q)=old r_q,
r_(0,q)=old l_q for every q, including arguments outside the sets. The
transition tile becomes

    ((1-d_j)*r_(0,u_j),h(q,b),d_j*r_(1,u_j),v_j),

which is the same ordered tuple at every one of the430 indices j+2.
The two copy rows become one, for d,b in{0,1},q in S_d:

    i=424+2*r_(d,q)+b,
    t_i=(d*r_(d,q),b,(1-d)*r_(d,q),h(q,b)).

At d=1 this is exactly the former right row, and at d=0 exactly the former
left row. Their rank intervals6..204 and205..249 are disjoint, so the whole
index coverage436..923 and every tuple remain unchanged, without a new
permutation or color conjugacy. The printed two-index r is a fixed function,
not the polynomial's scalar c or an additional unknown. The full d domain,
new rank definition, both extra transition subscripts and complete unified
row are present and charged in the body; no case table is left external.

## 2. Square-index the last nine tiles

The former final row used a label z in{0,1,4} and index
934+3*z+b-6*floor(z/4). Write z=a^2 for a=0,1,2. In those three cases
z-2*floor(z/4)=a, so the new index is934+3*a+b and the tile is
(a^2,437,b,437), with a,b=0,1,2. This covers each of934..942 exactly once
and reproduces the same nine tuples. It removes an unnecessary floor and
special label set. All other fixed control rows and the initializer remain
literal. Together with section1 every tile at every index0..942 is the same.

## 3. Cancel the artificial payload prefix

Put U(t)=w+2^8*n+2^17*e+2^25*s, as proof notation only. The former payload
was v_old=U+127*2^34; the new printed definition is v_new=2^34-U. Therefore

    (1+2^51)-2^10*v_old=1+2^10*v_new

identically for every tuple. The entire selector contribution can be written
G_943(x)+2^10*sum_(i=0)^942 v_new(t_i)*x^i. The four control groups are unchanged,
so this is the same complete Phi in Z[x], not an equality only at rho.
Every actual label is between0 and438, giving
U<=438*(1+2^8+2^17+2^25)=14754363318<2^34. Thus v_new is positive and at most
2^34; the selector coefficients are still positive and below rho. The support
indicator, both dummy holes and full low-mask identity remain unchanged.

Beta and MF have the same literal definitions; Lambda and the entire Phi
remain equal; hence MC and K remain equal too. The single source-high-mask
shift is unchanged. The whole ordinary native/Pell/refutation theorem applies
to the very same four integers and literal polynomial. This is no new compiler,
controller, proof-calculus calibration or consistency premise.

## 4. Complete source comparison and boundary

The entire marker-through-end-of-document body changes from3970 to3854 UTF-8 bytes,
and from3694 to3587 nonwhite source characters. These complete counts
include the full seed, alphabet, decoder, every new definition and every changed
row. The new body SHA256 isa62f4893e1554d12995c27ec5c542a993e01c1b11d9125352ae14fdb0a5dae17.

These are source-text metrics only. A complete printed-glyph comparison,
font/layout fit and readability remain unmeasured. No net rendered gain is
claimed, and no current page candidate is amended. The unified copy row uses
a substack to control its prospective width; its whole notation is included.
Any future implementation must parse the actual changed rank/set/tile/payload
expressions, prove all943 indexed tuples and the full Phi identity, reconstruct
all four raw integers, pass two complete static reviews and a separate execution
release, then pass full source/PDF audits, controls, rerenders and visual review.

All indices remain bounded constants. The dependency order is seed/actions,
sets/ranks/tiles, complemented payload and Phi, then the existing MC/K formulas;
Lambda and MF depend only on the fixed radix. There is no new recursion or
extra unknown. This proposal is separate from the currently held grouped66
checker repair; that exact page and its first execution requirements are unchanged.

## 5. Entire proposed constant body

```tex
\textbf{The four fixed integers.}
Every index, set, sum, product and floor below defines a constant, not
another unknown. Put
\[
\begin{gathered}
\rho=2^{67},\quad B=\rho^{8807},\quad\beta=B-1,\\
G_m(x)=\sum_{j=0}^{m-1}x^j,\quad
\Lambda=\rho^{4393}+\rho^{5495}.
\end{gathered}
\]
\begin{align*}
M_C={}&\beta+\rho-(\rho+3)\rho^{1063}\\
&-\sum_{e=0}^{3296}\fl{(D_\rho(\Phi(\rho),e)+\rho-1)/\rho}\rho^e,\\
M_F={}&B-1+4+(2^{51}-2)\Lambda\\
&+\rho^{1013}G_{10}(\rho)+\rho^{1065}G_9(\rho)
  +\rho^{2195}+\rho^{3296}\\
&+(2^{65}-1)\rho^{8792}G_{13}(\rho)+(2^{19}-1)\rho^{8805},\\
K={}&\rho^{30}+\rho^{62}+\rho^{1100}+\rho^{2201}+\rho^{8849}\\
&+\Lambda\Phi(1/\rho),
\end{align*}
where
\[
\begin{split}
\Phi(x)={}&G_{943}(x)+2^{10}\sum_{i=0}^{942}v(t_i)x^i\\
&+2^{10}x^{1003}(x^{20}+2^{17})G_8(2x)\\
&+2^{18}x^{983}(x^{30}+2^{17})G_9(2x)\\
&+2^{44}x^{992}(x^{39}+2x^{30}+4x^{19}+8)\\
&+2^{48}x^{1095}(1+2x^{1100}+4x^{2201}).
\end{split}
\]
The rational intermediate in K cancels exactly; all four results are positive integers.

\textbf{The 943 indexed fixed tiles.}
Use the actions $u_j,v_j,d_j$ decoded below. For $d=0,1$, let
\[
\begin{gathered}
h(q,b)=2(q+1)+b,\quad
\mathcal S_d=\{u_j:d_j=d,\ 0\le j<430\},\\
r_{d,q}=205-199d+|\mathcal S_d\cap\rg0{q-1}|.
\end{gathered}
\]
An interval ending at $-1$ is empty. The table defines $t_i$ for
$0\le i\le942$; all index ranges are fixed:
\[
\setlength{\arraycolsep}{1.4pt}\begin{array}{c|l}
\text{index }i&\text{tile }t_i=(w,n,e,s)\\\hline
0,1&(2,435,3,1),\ (5,0,0,0)\\
j+2\ (j=2q+b<430)&((1-d_j)r_{0,u_j},h(q,b),d_jr_{1,u_j},v_j)\\
432+b\ (b=0,1)&(0,h(215,b),0,h(215,b))\\
434+b\ (b=0,1)&(0,b,0,b)\\
\substack{424+2r_{d,q}+b\\q\in\mathcal S_d,\ d,b=0,1}&(dr_{d,q},b,(1-d)r_{d,q},h(q,b))\\
924+j\ (0\le j<4)&(0,j+430\fl{j/2},0,438)\\
928&(2,434,2,0)\\
929&(3,436,4,4)\\
930&(4,436,4,0)\\
497+t\ (t=434,435,436)&(1,438,1,t)\\
934+3a+b\ (a,b=0,1,2)&(a^2,437,b,437)
\end{array}
\]
For $t=(w,n,e,s)$ put
\[
v(t)=2^{34}-w-2^8n-2^{17}e-2^{25}s.
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
