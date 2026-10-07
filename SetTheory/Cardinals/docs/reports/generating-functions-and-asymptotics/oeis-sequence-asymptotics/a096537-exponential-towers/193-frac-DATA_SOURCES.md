# Sources and attribution

The mathematical definitions, exact recurrences, tree enumeration, and checks
are reproduced in Report193. No downloaded paper bodies or private research
materials are redistributed.

## Known family

Paul D. Hanna's OEIS A096537 and A096542 entries record the unshifted sequence
and the entire shifted functional equation and polynomial triangle:
- https://oeis.org/A096537
- https://oeis.org/A096542

A096542's formula line giving [y]P_n(y)=n a_n conflicts with the displayed rows
and defining equation. The latter imply [y]P_n(y)=n a_(n-1), independently
obtained by taking the coefficient of y in F_y=exp(x y F_(y+1)). The code uses
this derived identity, not the inconsistent line.

The leading unshifted equivalent appeared in the companion Report192. This
sequel explicitly states those leading facts and gives the quantitative
entrance, outer, Fourier and height-transfer arguments needed for the new
terms, including the offset Gamma factor.

## Earlier continued-exponential literature

C. M. Bender and J. P. Vinson, Summation of power series by continued
exponentials, Journal of Mathematical Physics 37 (1996), 4103-4119:
https://doi.org/10.1063/1.531619

D. Poland, Summation of series in statistical mechanics by continued
exponentials, Physica A 250 (1998), 394-422:
https://doi.org/10.1016/S0378-4371(97)00533-5

The broad continued-exponential/tree framework is prior. Primary metadata and
abstracts were inspected; complete full-text theorem overlap remains unresolved.
No unsuccessful search is used as a priority or novelty certificate.

## Analytic and arithmetic references

NIST DLMF, Airy initial values, Wronskians and connection formulas:
https://dlmf.nist.gov/9.2
Airy sector expansions and explicit real/complex remainder bounds:
https://dlmf.nist.gov/9.7
Airy zero locations:
https://dlmf.nist.gov/9.9
Gamma analytic properties, psi series and real Stirling remainders:
https://dlmf.nist.gov/5.2
https://dlmf.nist.gov/5.7.E4
https://dlmf.nist.gov/5.11.ii
Python Decimal documented arithmetic semantics:
https://docs.python.org/3/library/decimal.html

## Reproducible evidence

The three code/fixtures JSON files are regression targets from the directed
interval calculation. Their contents are regenerated or verified against full
recomputation on every mandatory replay. They are not empirical sequence fits.
The exact polynomial/tree checks are generated from two independent finite
combinatorial/algebraic constructions. No external data download is required.

Certified results are the broad interval and exact finite identities under
the documented arithmetic semantics. The ordinary estimate -0.43652529 is not
a certified decimal expansion and is not used as an input to the certificate.
