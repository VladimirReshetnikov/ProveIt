# Independent comparison of the 79 and 80 model routes

This source-level comparison finds no definite semantic contradiction in the reviewed coordinate changes, the exact zero-`w` algebraic cuts, or the displayed route interfaces. It does **not** establish that any Lean draft elaborates, that imported model lemmas have been rebuilt, or that an iPRA proof exists. The check pins nine exact input files; changing any invalidates its receipt. The 79/80 Lean graph transcriptions and 80-to-74 graph bridge are checked separately by [the 79 transcription review](../ordinary14-natural-forced-w79-lean-independent/README.md) and [the 80 partial-74 review](../ordinary14-natural80-partial74-bridge-independent/README.md).

The pinned 79 graph deletes exactly the 80 graph's row `w = n_w + 1`, replacing every use of `w` by `n_w`. Consequently, for arbitrary ring-valued 79 inputs `v`, its value matches the 80 graph at `v[6] - 1`, with all other slots unchanged. For natural-valued inputs the safe orientation is `v79[6] = v80[6] + 1`; 80 zero lifts to 79 unconditionally, while mapping a 79 zero back requires its coordinate 6 to be positive. Equal raw valuations do not give the claimed identity in general. The separate 80-to-74 projection preserves slots 0, 3, 8, 11 and 12, and adds one to the other nine, in particular the 74 variable `w` is positive even when the 80 coordinate 6 is zero. The 79 branch at coordinate 6 equal to zero is a different boundary case; its first Pell parameter `m = X Y²` is zero, so the 80 first-norm lemma requiring `m > 0` cannot be reused there.

At 79 `w = 0`, the checker derives exact polynomial identities from the literal graph, treating `Y`, `U`, and `R` as shared symbolic cuts. It confirms `X = ell = 0`, first factor `r²`, `a = Y`, `H = 4Y+3`, `Delta = H+Y²`, `c = (n_eta+1)+Y((n_eta+1)+(n_zeta+1))`, and

```
Dstar = U*Y*c + H*(U*gamma - ((n_eta+1)+n_zeta-R)).
```

If additionally `J=0`, the guard is `-((n_F+n_alpha+1)*K0+n_F)`, which is nonpositive for represented natural `K0`, including the boundary `K0=n_F=0`. It is not necessarily strictly negative. This matches the 79 client requiring represented natural `K0`, rather than `K0>0`. Its beta port must be represented by a positive natural. The 79 signed-quotient source separately requires positive `J`, obtained from the guard under those assumptions. The graph zero and all model/representation hypotheses remain essential.

The review checks two exact polynomial certificates used by the 79 divisibility argument. Given `U(d-Yc)=H z` and `d²=1+(H+Y²)c²`, they exhibit a ring witness for `H | U`. With `H=4Y+3`, `U=Yq²`, they exhibit a witness for `H | 3q²`. The displayed client further needs the signed-to-natural divisibility reflection and the inequalities `q≥2`, `Y≥q³`; those imply `0 < 3q² < 4Y+3`, a contradiction. The certificate itself does not prove the signed quotient, either root-sign case, reflection, or model inequalities.

For the 80 gamma route, the source instead requires representations of all four ports, positive beta and K0, `MC < beta`, and `MF < 2*beta`. It derives the positive partial-74 coordinates, the first and main norms, then calls the Pell/large-ordinate and narrow gamma lemmas. In particular, gamma positivity is a conclusion, not a premise. The assumptions and named calls are checked as pinned source text; no assurance of elaboration, source provider closure, nonstandard-model theorem validity, or axiom closure follows from those text checks. The source bodies and proof dependencies require independent kernel checking.

Reproduce from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-80-semantic-comparison-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-80-semantic-comparison-independent/result.json
```
