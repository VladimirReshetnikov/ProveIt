# Papers

Source papers for the `IntegerPoints` formalisation (the primitive circle
problem and the exponential-sum machinery behind it).  Every `.tex` file is an
OCR transcription of the printed paper, proofread by hand and by AI agents;
transcription slips were corrected, but typos that are consistent throughout a
paper (and hence probably in print) were left as they are and are listed in
the commit messages and in `docs/reports/`.  Where several OCR attempts of the
same paper existed, the best readings were merged into a single file.

The transcriptions are research aids for the proofs in `../Lean`; their
copyright remains with the respective publishers and authors, and they are
not covered by the repository's MIT-0 licence.

| File | Paper | Used for |
| --- | --- | --- |
| `On the number of coprime integer pairs within a circle.tex` | W. Zhai and X. Cao, *On the number of coprime integer pairs within a circle*, Acta Arith. 90 (1999), 1–16. | The main object of `IntegerPoints.ZhaiCao`: Lemmas 1–10, Propositions 1–2, the Theorem (exponent 11/30 under RH). Lemmas 1–6, 8 and 9 are proved in Lean. |
| `On the Primitive Circle Problem.tex` | J. Wu, *On the primitive circle problem*, Monatsh. Math. 135 (2002), 69–81. | `IntegerPoints.Wu`: Theorem 1 (exponent 221/608 under RH), Theorem 2, Lemmas 2.1 and 2.5–2.7, Propositions 1–4, the Vaughan identity (4.1). Lemma 2.1 and the Vaughan identity are proved in Lean. |
| `Exponential sums with monomials.tex` | É. Fouvry and H. Iwaniec, *Exponential sums with monomials*, J. Number Theory 33 (1989), 311–333. | Lemma 1 (the counting lemma) is Zhai–Cao's Lemma 6, proved in `IntegerPoints.FouvryIwaniec`; Proposition 1, Corollary 1, Theorems 1–7 and Lemmas 2–9 are stated in `IntegerPoints.FouvryIwaniecStatements`; Theorems 2–7 are the source of Wu's Lemmas 2.5–2.7. |
| `The method of exponent pairs.tex` | S. W. Graham and G. Kolesnik, *Van der Corput's Method of Exponential Sums*, Ch. 3 "The method of exponent pairs", LMS Lecture Note Series 126, Cambridge, 1991, pp. 21–37. | The definition of exponent pairs (`InGKClass`, `IsExponentPair`); Lemmas 3.1–3.7 are proved in `IntegerPoints.GKLemma31` through `IntegerPoints.GKLemma37` (Lemma 3.4 includes both curvature signs, Lemma 3.6 is the B-process transformation, and Lemma 3.7 has the exact book shift range); Theorem 3.8, the A-process, is proved in `IntegerPoints.AProcessTheorem`; equation (2.3.4), the Weyl–van der Corput inequality used in §3.3, is proved in `IntegerPoints.GKEq234`; and the invoked Theorem 2.1 estimate is proved in `IntegerPoints.GKTheorem21`. The invoked Theorem 2.2 and Appendix A estimates, Lemma 3.9, Theorem 3.10 (the exponent-pair B-process), and the remaining §3.3 claims remain statement-only in `IntegerPoints.GKStatements`. |
| `The distribution and moments of the error term in the Dirichlet divisor problem.tex` | D. R. Heath-Brown, *The distribution and moments of the error term in the Dirichlet divisor problem*, Acta Arith. 60 (1992), 389–415. | Theorems 1–6, Lemmas 1–6 and the truncated Voronoi formulas for `Δ(x)` and `P(x)` (needed for Nowak's formula and Wu's reduction to `ℛ(M, N)`) are stated in `IntegerPoints.HeathBrown`. |
| `Exponential sums and lattice points III.tex` | M. N. Huxley, *Exponential sums and lattice points III*, Proc. London Math. Soc. (3) 87 (2003), 591–609. | The unconditional circle-problem exponent 131/416; Hypothesis H, Propositions 1–6, Theorems 1–6 and Lemmas 2.3–2.5 are stated in `IntegerPoints.HuxleyStatements`. |
| `On the divisor and circle problems.tex` | H. Iwaniec and C. J. Mozzochi, *On the divisor and circle problems*, J. Number Theory 29 (1988), 60–93. | The exponent 7/22; the main theorems, the reductions, Lemma 11.1, Theorems 4.1 and 14.1 and the §6–§14 definitions are stated in `IntegerPoints.IwaniecMozzochi`. |
| `Partial fractions and four classical theorems of number theory.tex` | M. D. Hirschhorn, *Partial fractions and four classical theorems of number theory*, Amer. Math. Monthly 107 (2000), 260–264. | The four classical theorems and the partial-fraction identities are stated in `IntegerPoints.Hirschhorn`. |
| `On the method of exponent pairs.tex` | G. Kolesnik, *On the method of exponent pairs*, Acta Arith. 45 (1985), 115–143. | Multi-dimensional exponent pairs (Theorems 1–3) and the processes A and B for them (Theorems 4–5); the circle-problem exponent 139/429 and `ζ(1/2+it) ≪ t^{139/858}`; all stated in `IntegerPoints.Kolesnik`. |
| `The Circle Problem of Gauss and the Divisor Problem of Dirichlet - Still Unsolved.tex` | B. C. Berndt, S. Kim and A. Zaharescu, *The circle problem of Gauss and the divisor problem of Dirichlet—still unsolved*, Amer. Math. Monthly 125 (2018), 99–114. | Survey and history of the circle problem; its identities, Ω-results, moment asymptotics and the table of exponents are stated in `IntegerPoints.BerndtKimZaharescu`. |
| `The Lattice Points of a Circle.tex` | J. E. Littlewood and A. Walfisz, *The lattice points of a circle*, Proc. Roy. Soc. London A 106 (1924), 478–488. | The exponent 37/112 (with Landau's refinement `O(x^{37/112} log^{5/56} x)` in the appended note), the first application of van der Corput's method to the circle problem; the theorem, Lemmas 1–6 and Landau's note are stated in `IntegerPoints.LittlewoodWalfisz`. |

## Historical exponents for the circle problem

Upper bounds `P(x) = O(x^{θ+ε})` as listed in Berndt–Kim–Zaharescu (the
conjecture is `θ = 1/4`; Hardy proved `P(x) = Ω_±(x^{1/4})`):

| θ | Author(s), year |
| --- | --- |
| 1/2 | Gauss, c. 1800 |
| 1/3 | Sierpiński 1906; Landau 1913 |
| 33/100 | van der Corput 1923 |
| 37/112 | Littlewood–Walfisz 1924; Hardy 1925 |
| 163/494 | Walfisz 1927 |
| 27/82 | van der Corput 1928; Nieland 1928 |
| 15/46 | Titchmarsh 1934; Chih 1950; Richert 1953 |
| 13/40 | Hua 1942 |
| 12/37 | Chen 1963; Kolesnik 1969 |
| 346/1067, 35/108, 139/429 | Kolesnik 1973, 1982, 1985 |
| 7/22 | Iwaniec–Mozzochi 1988 |
| 23/73 | Huxley 1993 |
| 131/416 | Huxley 2003 |

For the primitive circle problem (coprime lattice points) the exponents are
`11/30` under RH (Zhai–Cao 1999) and `221/608` under RH (Wu 2002); these are
the statements formalised in `../Lean`.
