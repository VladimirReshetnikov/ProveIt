# Source notes and literature scope

Reviewed 1 October 2026. These notes distinguish established inputs from the new derivation in the report. They do not certify worldwide priority or repository-wide nonduplication.

## Established inputs

1. OEIS A113227 identifies permutations avoiding the vincular pattern 1-23-4 and credits the formal continued fraction to Sergei N. Gladkovskii on 10 October 2012. The entry inspected for this report contains no precise asymptotic formula: https://oeis.org/A113227
2. David Callan's 2010 paper supplies the exact two-index recurrence and valley-marked Dyck paths used in the proof: https://arxiv.org/abs/1008.2375
3. Beaton, Bouvel, Guerrini and Rinaldi supply the powered-Catalan name and further path/inversion-sequence descriptions. The formal fraction is prior art despite an older statement in their discussion about a lack of ordinary-generating-function information: https://arxiv.org/abs/1808.04114 and https://doi.org/10.1016/j.tcs.2019.02.003
4. Petreolle, Sokal and Zhu's general nonnegative Thron-fraction positivity theorem provides context. The report instead proves its finite positive measures directly: https://arxiv.org/abs/1807.03271, Theorem 9.9
5. The Bessel series, order reflection, Wronskian and Schlaefli integral are standard identities from DLMF Chapter 10, particularly 10.9.7: https://dlmf.nist.gov/10

## Earlier asymptotic question

Sergi Elizalde, Asymptotic enumeration of permutations avoiding generalized patterns, Advances in Applied Mathematics 36 (2006), 138-155, gives coefficient bounds in Proposition 6.1 and subfactorial growth in Corollary 6.2. Section 7 explicitly leaves precise asymptotics of 1-23-4 open. Verified DOI: https://doi.org/10.1016/j.aam.2005.05.006 ; preprint: https://arxiv.org/abs/math/0505254

## Later sources surveyed

The following provide generating trees, refinements, or bijections rather than the precise equivalent proved in the report:

- Duchi, Guerrini and Rinaldi (2018): https://doi.org/10.3233/FI-2018-1730
- Lin and Fu (2021), with the adjacent pair 12 underlined: https://doi.org/10.1016/j.ejc.2020.103282
- Cervetti (2022): https://doi.org/10.2478/puma-2022-0009
- Frosini, Guerrini and Rinaldi (2025): https://doi.org/10.3390/math13030517
- Testart (2025): https://arxiv.org/abs/2411.05726

Beaton's 7 February 2022 talk was also checked for an asymptotic result: https://clisby.net/brak/talks/RB2022_Nick.pdf

## Identification cautions

The pattern 12-34 is a different sequence. Classical or consecutive 1234 avoidance is different again. Avoidance of 110 in ascent sequences differs from avoidance of 110 in inversion sequences. B_n(e) is a Bell polynomial evaluated at e, not the ordinary Bell number. The new contribution claimed by the report is the rigorous positive Bessel spectrum and precise asymptotics, not the known fraction or general special-function machinery.

No third-party articles are redistributed in this archive; the report contains bibliography links.
