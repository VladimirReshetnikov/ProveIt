# Exact checks for the zero-tolerance torsion-packet theorem

Run from this directory:

```bash
python3 check_zero_tolerance.py --output checks.json
```

Dependencies: Python 3 and SymPy. The recorded run used SymPy 1.14.0. No network access is needed. All computations use integers, rational numbers, or finite fields; no floating-point tolerances are used.

## What is tested

1. **Initial-polynomial multiplicity and capacity.** For 81 triples `(p,e,h)`, enumerate every monic polynomial with nonzero constant coefficient over `F_p` whose exponent differences are multiples of `D=phi(p^h)/gcd(e,phi(p^h))`, up to the proposed minimal blocking degree. The program does not assume the root-capacity bound: it finds root multiplicities by repeated exact division by `X-a`. It then solves a weighted finite set-cover problem over all nonzero residue classes. The observed minimum total degree is `(p-1)p^max(h-1-v_p(e),0)`, giving budget `p^-min(v_p(e),h-1)`. There were 3,005 polynomials. Coefficients in larger finite residue fields are covered by the paper proof, not this enumeration.

2. **Cyclotomic initial relation.** Twelve exact shifted cyclotomic polynomials `Phi_(p^h)(1+T)` are reconstructed. Each has constant coefficient `p`, leading coefficient one, reduction `T^phi(p^h)` modulo `p`, and all intermediate weighted coefficient valuations strictly above one. This is an explicit check of the local relation `(zeta-1)^phi(p^h)/(-p) = 1` in the residue field.

3. **Explicit obstruction values, through resultants.** In twelve examples `K=Q_p(pi)` with `pi^e=-p`, put `k=min(v_p(e),h-1)`, `c=pi^(e/p^k)`, and `d=phi(p^h)/p^k`. The binomial is `T^d-c`. The program forms

   `R(U,Y)=Res_T(Phi_(p^h)(1+T),T^d-U-Y)`

   and

   `Q(Y)=Res_U(U^(p^k)+p,R(U,Y))`.

   The roots of the monic integer polynomial `Q` are all values `(zeta-1)^d-c'`, over every primitive `zeta` and every conjugate `c'`. For its degree `N`, every nonzero coefficient below the leading term satisfies

   `v_p([Y^j]Q) > (N-j)/p^k`.

   The Newton polygon therefore certifies that every nonzero root has valuation strictly greater than the witness valuation `1/p^k`; roots equal to zero also violate an upper valuation bound. This checks the actual obstruction values by a method distinct from the initial-polynomial proof. Full coefficients and all margins are included in `checks.json`.

4. **Cutoff comparison.** Twelve examples check the exact first strict budget crossing against the earlier `h0+floor(eB)` bound. The exact cutoff is the first `H` with the sum of shell costs strictly greater than `B`. Equality of cost with budget still permits a counterexample. The table includes pure tame, pure wild, mixed ramification, fractional budget, and late-shell cases where the old and new bounds agree.

## Results and evidence files

- `checks.json`: complete exact outputs and resultant certificates.
- `verification.log`: recorded successful run and compact table.
- `bound_comparison.csv`: comparison data.
- `bound_comparison.tex`: ready-to-include LaTeX table (requires booktabs).
- `summary.json`: small machine-readable summary.

All checks passed. They support and exercise the theorem; they do not replace its mathematical proof or establish literature priority.
