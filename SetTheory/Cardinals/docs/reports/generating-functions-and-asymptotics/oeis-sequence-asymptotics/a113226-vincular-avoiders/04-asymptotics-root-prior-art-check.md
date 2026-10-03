# Focused source and transform check, 1 October 2026

Sources inspected directly:
- OEIS A113226, https://oeis.org/A113226 : links Bevan–Cheon–Kitaev, Elizalde, Baxter/Pudwell; no displayed asymptotic formula or closed EGF.
- Bevan–Cheon–Kitaev, https://arxiv.org/html/2311.08023v2 and https://doi.org/10.1016/j.ejc.2024.104117 : Conjecture14 specifies factorial, exponential and n^(1/3) stretched-exponential form, with fitted constants. Proposition7 is the combinatorial foundation used here.
- OEIS A136127, https://oeis.org/A136127 : known excedance-set sequence, 2014 posted leading asymptotic, references including Testart2026. Its sequence and existing asymptotic are not claimed new.
- Benjamin Testart, On minimal pattern-containing inversion sequences, arXiv2602.12130v1, https://arxiv.org/html/2602.12130v1 , Section6 ending: A136127 counts inversion sequences equal to their reduction and is an antidiagonal sum of type-C poly-Bernoulli relatives. The paper states no simple formula is known. No A113226, 12–34, arcsine EGF or logarithmic-derivative relation found in the inspected paper.
- Targeted web queries A113226 generating function; naturally labelled arctan; 12–34 asymptotic2026 returned the above principal sources and old Callan/Elizalde papers, no later proof. Search absence is not exhaustive priority evidence.

## Exact connection to known poly-Bernoulli relatives
Testart's doubly exponential generating function is
T(x,y)=log[1/(e^x+e^y−e^(x+y))], with T_(a,b) for a,b≥1.
Its known antidiagonal identity is A136127(n)=Σ_(k=0)^(n−1) T_(k+1,n−k).
Our derived logarithm satisfies
L(z)=z+∫_0^z T_x(t,z−t)dt.
Since ∫_0^z t^(a−1)(z−t)^b/[(a−1)!b!]dt=z^(a+b)/(a+b)!,
ell_N=N![z^N]L=A136127(N−1), N≥2; ell1=1=A1361270.
Thus H′(z)/H(z) is the ordinary exponential generating function of A136127. This is an exact coefficient identity, not a fit. A direct combinatorial bijection explaining the exponential transform remains a worthwhile question.

The new research claim should be scoped to the derived A113226 EGF and its proved asymptotics/inverse, subject to full proof review and broader priority checking. Existing model, bijections, cumulant sequence and standard saddle methods must be credited.
