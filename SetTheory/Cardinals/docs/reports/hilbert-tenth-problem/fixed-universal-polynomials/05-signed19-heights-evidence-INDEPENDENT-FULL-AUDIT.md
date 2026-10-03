# Independent audit of the signed19 growth proof packet

Date: 3 October 2026. Verdict: **PASS, with the scope and limitations below.** No mathematical correction is required for the reviewed version, including its optional effective power-saving assertion.

## 1. Version and evidence binding

The final version reviewed is `PROOF-PACKET.md`, SHA256:

`ff9d116c90b058be082c2c9d6ee051ccf537d80821c14d10b28aec9a96d5a533`.

I independently read the full packet, its separate height and rotation notes, and the bound construction and construction-audit texts. Their byte hashes are:

- `HEIGHT-ASYMPTOTICS-CHECK.md`: `489e7b85b5329f3f40b0343183e61e9aa19fa844fe9d7143a265e51941278407`
- `rotation-counting-audit.md`: `6bade97d60715d04d68cb34fdd241aa923c03ae0b7cebc788d201cc568f32542`
- `evidence/FULL-SIGNED-COUNTEREXAMPLE.md`: `b109e2fd1142cdad84a5b519acc5dc5055160f1d8e7617d648a561538fd956cd`
- `evidence/CONSTRUCTION-INDEPENDENT-AUDIT.md`: `cd62529a6efcdfcbab43f1426c6b3fe5930575fda2cc865f12c40a5ec6c3bda6`
- `context/Research_Report25.tex`: `8c726653a01afc017b1bec52437f01824e07d82742713a094043c284c30b77b7`

All three hashes stated in the proof packet match their files. Report25's scope, main classification and counting statements were checked directly for the comparison in Section 5; this is not a fresh audit of that entire article.

Only inert source text was read. No upstream code or arithmetic schedule was executed, no repository file was changed, and this new audit note is the only file written by this audit.

## 2. Scope and construction dependence

The theorem fixes the compiler export, positive input, repunit and prime/scale choice. It counts exactly the canonical auxiliary prescription on one CRT progression, with the prescribed first-Pell congruence and strict ratio condition. It does not count the whole signed19 fiber.

The source formulas agree with the packet: the main step is `V=T Q H0`, the first-Pell modulus is `L=E/2`, `c=psi_A(p)`, `m=pc`, `Qaux=Delta psi_A(m)`, and `S=p+2m`. The main and first quadratic fields are distinct: the squarefree part of `Delta` is odd, whereas that of `P^2-1` is even. This supplies both the irrational rotation step and the field intersection used at the endpoints.

Distinct selected values of `p` give distinct tuples; the source's `Z` already grows affinely and injectively in `p`. The later strict height monotonicity gives an additional independent no-ties argument. All retained source coordinates are accounted for; omitted/computed registers are not mistakenly included in the supplied-coordinate maximum.

## 3. Exact endpoints, phase and density

Writing `M=L beta`, inversion of the positive increasing function `sinh(n beta)` gives exactly the open interval `(a_p,b_p)` printed in Section 1. The inequality

`0 < b_p-a_p < log((Y+1)/Y) < M`

is valid. In particular, uniqueness is true before any asymptotic replacement of the interval. All possible large-index solutions satisfy `n=(alpha/beta)p+O(1)` and are positive.

Expanding the endpoints independently gives

`epsilon_q(p)=(4q^2 Delta/Dp-1) exp(-2alpha p)+O(exp(-4alpha p))`.

The coefficient includes both the negative Binet correction and the positive inverse-hyperbolic correction. Neither is missing.

The proof packet uses the upper endpoint for its phase. If `u=(alpha p+g-log Y-n0 beta)/M`, the limiting interval contains an admissible lattice point exactly when there is an integer `v` with `u-d_rot<v<u`, equivalently `{u} in (0,d_rot)`. Thus the phase and open interval in the packet are correct. The rotation note instead uses the lower endpoint and `(1-d_rot,1)`; those are equivalent conventions, not a discrepancy between the proofs.

Equidistribution plus shrinking neighborhoods of the two endpoints correctly proves the density without assuming finite mismatch. Consequently the density within the progression is `d_rot=delta/(L beta)`, the density among integer main indices is `d_rot/V`, and the leading height-count constant is exactly

`kappa=d_rot/(2alpha V)=delta/(2alpha V L beta)`.

## 4. Height dominance, monotonicity and expansion

The auxiliary norm gives `U<y` for `y>1`; then `j=(U-p)/c<y`. The exact relation `q^2=Delta(f^2-1)` gives `f<q`, and `q=i c^2` gives `i<=q`. Since `S>=3`, one also has `y>=4q^2-1>q>=c^2`. Finally `o=(U+c)/f<(y+c)/2<y`. These are valid on the integer canonical family.

The remaining varying coordinates are `O(c+p+1)`, with fixed implied constants: the strict ratio bounds `k`, `eta` and `zeta`; the first norm bounds `tau`; the formulas bound `h`, `sigma`, `Z` and `rho`. The other supplied coordinates are fixed. Exponential growth of `c` and `y>=4c^4-1` therefore prove strict eventual dominance by `y`, even if some fixed source coordinates are very large.

The real extension is valid for all `p>=1`: `m,q,S` increase and `q(1)=Delta>=3`. The quotient `sinh(Sb)/sinh b` increases strictly in both `S>1` and `b>0`, since `z coth z` is strictly increasing. Hence `y(p)` is strictly increasing, which validates a unique real cutoff and the ranked-height statements.

For `d=sqrt(Delta)` and `ell=log d`, direct expansion gives

`log y=(2m+p-1)(alpha m+ell)+O((m+p)exp(-2alpha m))`.

After inserting `m=p(exp(alpha p)-exp(-alpha p))/(2d)`, the first two scales are

`[alpha/(2Delta)]p^2 exp(2alpha p)`

and

`[p/(2d)][alpha(p-1)+log Delta]exp(alpha p)`.

Thus the first exponential correction to `loglog y` is exactly

`d[1+(log Delta/alpha-1)/p]exp(-alpha p)`.

The remaining error is `O(exp(-2alpha p))`, as asserted. The constant `C=alpha/(2Delta)` and both displayed leading height laws pass.

## 5. Lambert W cutoff and floors

The leading model has the exact inverse

`t_B=alpha^(-1) W(sqrt(2alpha Delta log B))`.

The perturbation argument is valid: bracket `p_B-t_B` by `O(exp(-alpha t_B))`, use the derivative `2alpha+2/t_B` of the leading logarithmic model, and Taylor-expand the explicit first correction. This yields exactly equation (3), including its negative sign and its `O(exp(-2alpha t_B))` residual. In particular `p_B<t_B` eventually.

The ordinary inverse expansion has the correct constant `log(8alpha Delta)`. The finite-width progression discrepancy from replacing `p_B` by `t_B` is at most one eventually, but not identically zero at all jumps. The packet correctly keeps the true inverse in its exact floor formula.

## 6. Independently verified external inputs

I independently opened the research papers below rather than accepting the other notes' descriptions.

### Fixed algebraic logarithms

[Bugeaud, *B′*, Theorem 1.1, equation (1.2), printed p. 2](https://arxiv.org/pdf/2209.00275) gives a lower bound for a nonzero logarithmic form that is linear in `log B` once the algebraic numbers are fixed. The observation immediately afterward on p. 3 explicitly reduces it to `|Lambda|>=B^(-C)`. The hypotheses allow integer coefficients; there is no required multiplicative-independence hypothesis beyond nonvanishing of the particular form. The constants are effective. This is sufficient for both applications here. Bugeaud cites Baker–Wüstholz in connection with the standard bound, while attributing the collected Theorem 1.1 estimates to Waldschmidt and Matveev. The original Baker–Wüstholz publisher page did not load in this audit; no direct reading of its full text is claimed. The explicit research-paper theorem was successfully verified.

### Fixed-phase bounded remainder

[Kelly–Sadun, Theorem 1, printed p. 1](https://arxiv.org/pdf/1404.0455), also available in [HTML](https://arxiv.org/html/1404.0455v2), gives bounded interval discrepancy exactly when the interval length lies in the additive group generated by the irrational step and 1. Its setup allows an arbitrary starting point. Equivalently, one translates the interval by the phase, preserving its length. The displayed source convention includes the endpoint index `N`; its difference from a sum over `0<=r<R` is bounded and irrelevant here. Irrationality also limits changes from interval endpoint conventions to at most two orbit hits. The theorem therefore applies to the particular fixed phase in this packet, not merely almost every phase or a phase average.

### Erdős–Turán

[Part I, Theorem III, printed p. 1150](https://www.renyi.hu/~p_erdos/1948-02.pdf) states the required finite discrepancy estimate; its proof is in [Part II](https://www.renyi.hu/~p_erdos/1948-03.pdf). The same inequality is explicitly restated in [Erdős–Koksma, Lemma 2, printed p. 300](https://users.renyi.hu/~p_erdos/1949-11.pdf). Their normalized-discrepancy convention becomes the packet's `R/(K+1)` plus weighted exponential sums after multiplication by `R`. Replacing `K+1` by `K` in big-O for `K>=1` is harmless.

## 7. Eventual exact rotation representation

For either endpoint, the packet's form is

`Lambda_q=p log lambda-n log nu+log(sqrt(Dp)/(2q sqrt(Delta)))`.

If it vanished, squaring the positive multiplicative identity would place `lambda^(2p)` in the intersection of the two distinct quadratic fields. It would be rational. Its norm then forces it to equal 1, impossible for positive `p`. Thus the nonvanishing hypothesis of the logarithmic-form theorem has been proved, not assumed.

Only integers with `n=(alpha/beta)p+O(1)` can approach these endpoints. Their logarithmic-form coefficients are `O(p)`, giving a uniform fixed-parameter lower bound `c p^(-C)` at both endpoints. This eventually exceeds the exponentially small endpoint shifts. Consequently exact and limiting indicators coincide for every index in a sufficiently late progression tail.

Choose the tail after this threshold and after positivity and height dominance. Then the formula

`N(B)=d_rot R(B)+D(R(B))`

is genuinely exact, with the printed `R(B)=max(0,1+floor((p_B-p_b)/V))`. A different finite initial convention introduces only a fixed count offset. Combining it with the inverse height expansion gives equation (5) with a bounded residual, uniformly over all sufficiently large real height cutoffs.

## 8. Second coefficient: necessity, sufficiency and obstruction

The packet's displayed decomposition proves the precise equivalence

`N(B)=kappa t-2kappa log t+o(log t)` for all large real `B`, with `t=loglog B`,

if and only if

`D(R)=o(log R)` as integer `R` tends to infinity.

Sufficiency follows because `R(B)~t/(2alpha V)`. For necessity, take `B=y(p_b+V(R-1))`; monotonicity gives exactly `R(B)=R`, and `log t=log R+O(1)`. This explicitly fills out the necessity assertion implicit in the theorem and stated in the separate rotation note. No revision is needed, though adding this one-line equivalence would make the main packet still clearer.

The non-bounded-remainder argument also passes. If `d_rot` were in `Z+theta Z`, exponentiating the resulting logarithmic relation would make the rational number `(Y+1)/Y>1` an algebraic unit. A rational algebraic unit is only `1` or `-1`, a contradiction. Kesten then makes the fixed-phase discrepancy unbounded. Since `R(B)` attains every sufficiently large integer and the remaining term in equation (5) is bounded, the proposed smooth two-term count with `O(1)` remainder is impossible.

Unbounded discrepancy does not by itself contradict `o(log R)`. The packet correctly leaves that finer assertion unresolved. Neither equidistribution nor the power-saving estimate proves the stated second coefficient.

## 9. Optional effective errors and ranked inversion

For the nearest integer `k` to `h theta`, irrationality ensures that `h V alpha-k L beta` is nonzero. The two-logarithm bound therefore gives `||h theta||>=c h^(-mu)` for some effective `mu>=1`, after weakening the exponent if needed. The geometric-series estimate and Erdős–Turán give

`|D(R)| << R/K+K^mu`.

With `K` of order `R^(1/(mu+1))`, this is `O(R^(1-eta))`, where `eta=1/(mu+1)>0`. The leading count follows because `R(B)` is of order `t`; the analytic `log t` correction is absorbed by this error. Because heights have no ties, `j=N(B_j)` exactly for the chosen tail. First use `t_j~j/kappa`, then substitute into the error to obtain `t_j=j/kappa+O(j^(1-eta))`. Assertion 5 passes in both its counting and ranked forms.

The effective exponent is allowed to be tiny and all constants depend on the fixed construction. This gives no parameter-uniform estimate or practically useful numerical onset.

## 10. Final limitations

This PASS certifies the mathematical growth/counting claims for the specified canonical fixed-scale subfamily and the stated external-theorem applications. It does not classify all negative-restoration witnesses, count the entire signed19 fiber, identify false machine acceptance, materialize a complete large witness, improve a universal representation bound, or establish publication novelty. The comparison to Report25 respects these distinctions. The main remaining counting question is the finer discrepancy scale needed for the triple-logarithmic second term.
