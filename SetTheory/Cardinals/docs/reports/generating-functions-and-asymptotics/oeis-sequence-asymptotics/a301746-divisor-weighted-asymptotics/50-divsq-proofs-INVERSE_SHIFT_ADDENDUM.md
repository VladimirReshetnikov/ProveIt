# Proposed first inverse saddle shift

Separate addendum for review; PROOF_NOTES.md remains frozen at SHA256 73aa3cb2a481d8c50dd56422fd9d73c2c179e90ab68d2e0aa223aa73d6979231.

Let g(x)=log A_0(x), C_1(t)=κ_4/(8V²)−5κ_3²/(24V³), and h(x)=log(1+C_1(t_x)). Define x_0=A_0^{-1}(y), x_1=A_1^{-1}(y), t=t_{x_0}, L=log(1/t), and M=t^{-1}L³. Then

x_1=x_0−h(x_0)/g'(x_0)+O(1/(tM³))
   =x_0−C_1(t)/t+O(1/(tM²))
   =x_0+9/(4L³)(1+O(1/L)).

Proof. The established derivative rules give

g'~t, g''=O(t²/M), C_1=O(M^{-1}), h'=O(tM^{-2}).

The derivative bound for g'' follows by differentiating g'=t−κ_3/(2V²), using t'=-1/V and κ_r'=κ_{r+1}/V. The implicit equation g(x_1)+h(x_1)=g(x_0) first gives Δ=x_1−x_0=O(1/(tM)); local t and M are comparable because this Δ is o(x_0). Taylor expansion then gives

g'Δ+h(x_0)=O((t²/M)Δ²+(t/M²)|Δ|)=O(M^{-3}).

Divide by g'~t to obtain the first formula. Since h=C_1+O(M^{-2}) and g'=t(1+O(M^{-1})), the second follows. The first-cumulant asymptotic C_1=−9t/(4L³)(1+O(1/L)) proves the last formula.

Combining the second formula with the R=1 threshold brackets gives the especially usable form

ceil(x_0−C_1(t)/t−C t/L^6)≤N(y)≤ceil(x_0−C_1(t)/t+C t/L^6)

for a suitable C and all sufficiently large y. Unlike replacing C_1 by its −9t/(4L³) equivalent, retaining exact C_1 preserves this small certified error scale.
