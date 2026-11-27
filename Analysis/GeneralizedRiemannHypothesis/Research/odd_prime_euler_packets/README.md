# Odd-prime Euler-factor packets: a partial solution of the article's open question

- `odd_prime_euler_packets.tex` — full self-contained finite-algebra proofs and a GRH transfer using the article's prime Gram lemma.
- `odd_prime_euler_packets.pdf` — compiled research note.
- `verify.py`, `verification.txt` — reproducible exact arithmetic enumeration and construction tests.
- `source-audit.md` — inspected repository interfaces, source identifiers and novelty boundaries.
- `formalization-roadmap.md` — precise finite-algebra and analytic dependency plan (not a Lean proof).

## Reproduction

Run `python3 verify.py` with the standard library only. To rebuild the PDF, run `pdflatex -interaction=nonstopmode -halt-on-error odd_prime_euler_packets.tex` twice. The finite checks do not rely on floating point or GRH.

## Main results

For equal-degree distinct packets of characters of exponent a prime `ell`, the disagreement density is at least `(ell-1)/(ell*k)`. Equality is exactly the disjoint parallel full-coset construction; in particular this determines the exact minimum for every prime-power packet size less than the size of the character group. For rank at least 2 and `k<=ell`, the sharper pencil bound is `(ell-1)*(ell+1-k)/ell^2`, attained for divisors of `ell-1`, proper divisors of `ell+1`, and `k=ell`. The first two possible positive disagreement levels have exact thresholds. A GRH prime-window certificate has a uniform scale quadratic in packet size and logarithm of the modulus; an extremal density can be measured at that scale. The finite algebra is unconditional. The analytic transfer is conditional on the exact vendored Dirichlet GRH statement, taken as input here.

No files in the GitHub repository were modified. No new Lean proof was compiled. Literature-wide priority and the complete odd-order density spectrum are not established.
