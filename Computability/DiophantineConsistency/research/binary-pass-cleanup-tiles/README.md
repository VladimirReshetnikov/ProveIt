# A floor-free fixed tile table with one fewer row

CODE-FREE ORDINARY PROPOSAL; independent review and future rendering are
pending. Four elementary rewrites shorten the accepted compact-parameter
constant body from3854 to3819 UTF-8 bytes and3587 to3555 nonwhite source
characters. They preserve every943 indexed tile, all430 actions, the full
436-character seed, the complete four integers and the fifteen-positive
66-operation, degree157 polynomial. These are source metrics, not rendered
measurements. No application import, compilation, execution, tuple/decoder
generation, standalone TeX/PDF, Lean work or page change occurs here.

The main changes merge the four halt/plain pass tiles into one row and
remove the final floor from the tile table's cleanup row. Two small
algebraic rewrites remove head-label parentheses and one operation from
the fixed flag decoder. The selected full body is printed below as inert
text; every domain, new subscript, seed character and unchanged constant
formula is included. The accepted compact and held grouped66 packages
remain separate and unchanged.

## 1. Merge the four pass tiles with an explicit inverse

The old two rows, for b=0,1, were

    i=432+b, t_i=(0,h(215,b),0,h(215,b)),
    i=434+b, t_i=(0,b,0,b).

Since h(215,b)=432+b, replace them by the single row

    i=434-2a+b, t_i=(0,432a+b,0,432a+b), a,b=0,1.

At a=0 this gives exactly the old plain passes at434,435; at a=1 it
gives exactly the halt passes at432,433. The four cases are complete:

| a | b | i | Ordered tile |
|---|---|---|---|
| 0 | 0 | 434 | (0,0,0,0) |
| 0 | 1 | 435 | (0,1,0,1) |
| 1 | 0 | 432 | (0,432,0,432) |
| 1 | 1 | 433 | (0,433,0,433) |

For any432<=i<=435, put j=i-432, b=j mod2 and a=1-floor(j/2).
Then a,b are binary and434-2a+b=i. This is the unique inverse; the
rewrite does not reorder selector indices or alter the ordered coordinates.
Both domains are explicitly printed in the new row. Its local a,b are
fixed indices, independent of the polynomial's abbreviations and of other
rows' separate local indices.

## 2. Remove the cleanup floor by a binary decomposition

The old cleanup row at924+j,0<=j<4, was

    (0,j+430*floor(j/2),0,438).

Every such j has the unique form2a+b, with a,b=0,1. Hence
j+430*floor(j/2)=2a+b+430a=432a+b. The exact new row is

    i=924+2a+b, t_i=(0,432a+b,0,438), a,b=0,1.

For i=924,925,926,927 the recovered(a,b) are(0,0),(0,1),(1,0),(1,1),
so the north labels are0,1,432,433, as before. The inverse is
j=i-924,a=floor(j/2),b=j mod2. Those floors are proof notation only;
none remains in the printed row. Both binary domains are fully charged.

All other table rows are copied exactly from the compact parent. Its
merged direction/copy family and square-indexed terminal nine tiles stay
unchanged. The index partition remains0..1,2..431,432..435,436..923,
924..927,928..930,931..933,934..942. Thus every one of the943 tuples
is preserved at the identical index. The three literal control tiles at
928..930, including constructor(3,436,4,4), and the three tail tiles at
931..933 remain literal. The table now has ten parameterized/literal rows
instead of eleven and contains no floor at all.

## 3. Two ordinary algebraic simplifications

Replace only h(q,b)=2(q+1)+b by h(q,b)=2q+b+2. Distributivity proves
this for all integers q,b, hence for every transition/copy target and
constructor check. Its arithmetic-operation count is unchanged; two
parentheses disappear. In particular h(1,0)=4 remains the actual first
target label, and h(215,b)=432+b remains the pass identity above.

In the unchanged430-action decoder replace

    F_q=14*(1-m_q)+m_q*D_16(E0,tau_q)

by

    F_q=14+m_q*(D_16(E0,tau_q)-14).

Distributing m_q proves equality for arbitrary integers m_q and digit
values. At actual m_q=0 or1 it still selects14 or the same stored nibble.
Consequently every v_j,d_j remains identical; u_j and all remaining
decoder definitions are copied verbatim. The old local expression has
one subtraction, two multiplications and one addition; the new one has
one subtraction, one multiplication and one addition. This saves one
fixed-decoder arithmetic operation. It changes none of the polynomial's
66 operations and introduces no new fixed abbreviation or unknown.

## 4. Whole constants, exact comparison and rejected variants

The head-label identity and two bijective row rewrites preserve the entire
indexed table pointwise. The factored flag formula preserves all actions
pointwise from the same literal seed. Therefore the compact parent's
complemented payload at every tile and its complete Phi polynomial are
identical. All control coefficients, support/dummy positions, Lambda,
beta and the full MC/MF/K definitions stay literal. Their four integers,
including the single source-high-mask shift, are equal as whole integers.
The accepted295388 canonical raw bytes and ordinary native/Pell/refutation
calibration apply to the same tuple and polynomial. No isolated coefficient
substitution, fresh controller or new calibration premise occurs.

The following exact replacements are the entire source difference. Each
saving is charged including row domains, separators and all notation:

| Change | Old bytes | New bytes | Byte saving | Nonwhite saving |
|---|---:|---:|---:|---:|
| head label | 15 | 13 | 2 | 2 |
| two pass rows to one | 67 | 41 | 26 | 24 |
| binary cleanup row | 43 | 38 | 5 | 4 |
| factored default nibble | 35 | 33 | 2 | 2 |
| Complete body | 3854 | 3819 | 35 | 32 |

The whole old/new body nonwhite counts are3587 and3555. These count the
entire marker-through-document-ending body, including all430-action
formulas,436 seed characters,62-symbol alphabet, domains, table, footer
and unchanged fixed formulas. They are exact source-text arithmetic; no
rendered glyph count, page fit or readability has been measured.

Two other exact identities were considered but are not selected. The
three control rows928..930 can be written as

    928+j, (j+2,434+j*(3-j),2+j*(3-j),4*j*(2-j)), j=0,1,2.

Its three cases reproduce the literal tiles, but its complete row is52
source bytes versus53 for the three literal rows. Saving one source byte
while adding repeated arithmetic makes this an unhelpful complexity
tradeoff. The selected full body retains the three literal rows.

A shared quotient Q=floor(A/2^636),T0=Q mod2^1675,
E0=floor(Q/2^1675) is also correct, since nested integer quotients give
the old E0=floor(A/2^2311). After paying the entire Q definition and
all uses, the replacement block is107 source bytes versus106, one
nonwhite character longer as well. It is not selected. No seed repacking
or mixed-radix399 proposal is repeated here. These bounded comparisons
make no global optimality claim.

The new dependency order remains fixed seed/actions, sets/ranks/tiles,
complemented payload/Phi, then MC/K; Lambda and MF depend only on the
radix. There is no recursion. Any future implementation must parse the
actual changed table/head/flag expressions with their local scopes,
prove all943 pointwise tuples and all430 decoded actions, reconstruct
every raw integer byte, pass independent full reviews and a separate
execution release, then pass complete actual-TeX/PDF audits, controls,
pure rerenders and independent visual inspection. This ordinary note
releases none of that execution or promotion work.

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
h(q,b)=2q+b+2,\quad
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
434-2a+b\ (a,b=0,1)&(0,432a+b,0,432a+b)\\
\substack{424+2r_{d,q}+b\\q\in\mathcal S_d,\ d,b=0,1}&(dr_{d,q},b,(1-d)r_{d,q},h(q,b))\\
924+2a+b\ (a,b=0,1)&(0,432a+b,0,438)\\
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
F_q=14+m_q(D_{16}(E_0,\tau_q)-14),\\
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
