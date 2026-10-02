# Integrated mathematical and source-fidelity review

Date: 1 October 2026 (UTC).

Verdict: **PASS. No mathematical error or mathematical repair was identified.** This is a fresh integrated review of the addendum's transcription, logical scope, and new reciprocal/first-sector arguments, not a replacement audit of the original combinatorial theorem.

Reviewed `fixed-sector-addendum.tex` SHA-256:

`00fc2ddc682aad5dd913a3d57d522574f1f8e05a76f56c104b87f7342586a560`

## Source identity and scope

The included derivation has SHA-256 `eb796ae1044a019737f7c5af20cc2a217f8e95bbdffa25c17ab565ae23632d3d`. The included independent PASS audit has the requested SHA-256 `a6b79f52cce12441c5d6b7d3c7f37583f4dbdd312f9f75616c06ee63ad71bbe1`. Every included source hash and both separately delivered main-report hashes match `provenance.json`.

The main report's fixed-cap growth-constant identification, cap-two dependency, first-variation error, controlled length inverse, and rounding-safe cap inverse are accurately described. The addendum does not claim to reprove the combinatorial identification, improve length asymptotics, or supply a sharper cap inverse. Referencing the separately delivered main report without duplicating it is consistent with the stated scope.

## Mathematical integration

- The exact positive sector decomposition, positive finite remainder, geometric sandwich, large-v bound, and successive-sector relative error agree with the source. Every asymptotic assertion retains its fixed-K, fixed-r, or fixed-N quantifier; the exact infinite identity is not used to sum asymptotic sector formulas.
- The derivative identity and error, uniform tail expansion and recurrence, saddle/curvature, localization, leading constants, all-orders remainder, rationality argument, and finite coefficient algorithm are faithfully transcribed. In particular the Gaussian phase and Stirling exponents and the conversion from m=b+1 to b are correct.
- All displayed r=2 and r=3 coefficients agree with both reference coefficient arrays. A fresh symbolic check confirms the general first-coefficient formula at r=1,2,3,4. Every displayed numerical-table entry is the correctly rounded value of the author reference JSON. The author and independent saved coefficient arrays agree exactly.
- The exact first-sector derivation is valid: F(k)=1/[(k-1)k^m] and -(k-1)F'(k)-F(k)=m k^(-m-1). Replacing the linear factor by its stated absolute bound produces the summable integral m k^(-m-1)+2/[(k-1)k^m], so the interchange is justified. Thus A_(1,b)=m(zeta(m+1)-1) and J_(1,b)=m/2^(m+1), including the displayed algebraic coefficient exceptions.
- The new reciprocal corollary is correct. The exact nonlinear correction is -delta_b^2/[tau^2(tau+delta_b)], with delta_b=O(b 2^(-b)), hence O(b^2 4^(-b)). For every fixed K this is exponentially smaller than A_(K+2,b), because beta_(K+2)>e^(-1)>1/4. It can therefore be absorbed into the stated relative remainder after A_(K+1,b). The conclusion is eventual positivity for each fixed K; the addendum correctly avoids asserting positivity for all b. The leading deficit constant 9(b+1)/(pi^4 2^b) is correct.
- The warning about finite algebraic truncations overwhelming later sectors is retained with the correct error powers. No growing-sector uniformity, optimal truncation, summability, accumulation-scale theorem, or complete smaller-scale transseries is claimed.

## Reproducibility descriptions

The descriptions of local Gaussian, independent discrete-geometric, exact rational integration, and Gamma-centered calculations match the included scripts. Their distinct ranges are represented accurately: independent rational J checks at r=2,3 and b=50,100,200; author J quadratures also at b=500; exact A quadratures at r=1,2,3 and b=20,50,100; derivative checks through r=6; exact J1 checks through b=30. The quadratures are explicitly not interval-certified proofs. The claimed original byte-identical author rerun is recorded by the included audit; current staged author and independent replay JSON also match their reference files byte for byte.

The new `verify.sh` writes to `checks/replay`, compares the source and Gamma reference outputs, requires the independent aggregate PASS flag, and adds a reciprocal-algebra check. Final archive completeness, clean-unpack replay, PDF visual QA, and release checksums are separately verified by the packaging workflow; this verdict concerns the mathematics, source fidelity, and stated reproducibility scope.
