# Statement audit

Source snapshot: Wikipedia revision `1348379317`, last edited April 12, 2026.

| Source-page assertion | Result in this packet |
|---|---|
| Local inverse coefficient formula for analytic `f` with `f'(a) != 0` | Proved coefficientwise; the derivative/limit display is recovered exactly. |
| Nonzero analytic radius | Proved for primitive-recursively named analytic data with an explicit rational lower bound obtained by contraction. |
| Formal power series form | Proved as a uniform finite theorem in `R[X]/(X^(N+1))`. |
| Formula for `H(g(z))` | Both displayed Lagrange-Buermann forms are proved. |
| Several-variable extension | Good's determinant formula is proved by finite multivariate residues. |
| Case `f'(a)=0` | Ramified/Puiseux branches are constructed after adjoining the needed algebraic roots. |
| Bell polynomial formula | Proved by a finite negative-binomial and partial-Bell expansion. |
| Associahedron formula | The standard ordinary-coefficient formula is proved. The displayed page formula is inconsistent with the immediately preceding exponential convention; a corrected translation and degree-two countercheck are supplied. |
| `x^p-x+z=0` | Displayed coefficient formula, boundary convergence, and largest centered inverse disk are proved. |
| Lambert W at zero | Displayed coefficients and exact radius `e^-1` are proved. |
| Shifted Lambert W | Displayed coefficients (plus one extra term), exact radius `sqrt(4+pi^2)`, real interval, and an exact `W(1)` enclosure are proved. |
| Binary trees | Catalan formula is proved for plane rooted full binary trees with unlabelled nodes. The order/plane qualification is necessary for `B=1+zB^2`. |
| Laplace-Erdelyi use | The inversion coefficient step and finite constructive remainder route are made explicit. |

## Two source wording issues

1. **Associahedra.** If
   `f(w)=sum f_n w^n/n!` and `g(z)=sum g_n z^n/n!` with `f_1=1`, define
   `c_m=f_(m+1)/(m+1)!` and `d_m=g_(m+1)/(m+1)!`. The standard face theorem
   applies to `c_m,d_m`, not directly to unshifted `f_i,g_i`. For
   `f(w)=w+c w^2/2`, the correct inverse coefficient is `g_2=-c`, which the
   page's displayed normalization does not reproduce.

2. **The alternative `H(g)` formula.** The displayed formula is correct. The
   prose immediately before it informally says that `H'` is replaced by
   `H(1-phi'/phi)`; the actual factor contains the variable:
   `H(w) phi(w)^(n-1) (phi(w)-w phi'(w))`.
