# Computational and fixture provenance

## Primary mathematical sources

**Endpoint recurrence.** Anders Claesson, Bjarki Ágúst Guðmundsson, Jay Pantone,
*Counting pop-stacked permutations in polynomial time*,
[arXiv:1908.08910](https://arxiv.org/abs/1908.08910),
[author PDF](https://akc.is/papers/033-Counting-pop-stacked-permutations-in-polynomial-time.pdf),
[DOI 10.1080/10586458.2021.1926001](https://doi.org/10.1080/10586458.2021.1926001).
`endpoint_run_polynomials` implements the run-refined recurrence (3), printed
p.4, using prefix sums in the two endpoint coordinates as described on p.5.
The implementation is an adaptation of the audit computation listed below,
not a copy of the authors' repository implementation.

The source PDF examined for the recurrence had SHA-256
`e822a3fc535b5ca7950bbb8efc6222cd4f5dfcdfe940065cc2105c43e7d601fc`.

**Fixed-run rational fixtures.** Andrei Asinowski, Cyril Banderier, Benjamin Hackl,
*Flip-sort and combinatorial aspects of pop-stack sorting*, DMTCS 22:2 (2021),
[primary article](https://dmtcs.episciences.org/7411),
[primary PDF](https://dmtcs.episciences.org/7411/pdf),
[DOI 10.46298/dmtcs.6196](https://doi.org/10.46298/dmtcs.6196).
Printed p.10 displays all five formulas. That page is the fixture source.
Theorem 6, printed p.8, proves prior fixed-run rationality. Notation `P_k(z)` in
that paper is renamed `F_k(x)` here, so it is not confused with the bivariate EGF.
The variable rename and expansion of the integer numerators are the only
normalizations applied to these fixtures.

For `D_k(x)=product_{j=1}^k (1-j*x)^(k-j+1)`, the fixtures are:

```text
N_1(x) = x
N_2(x) = 2x^3
N_3(x) = 2x^4(1+3x-6x^2)
N_4(x) = 2x^6(21-74x+5x^2+180x^3-144x^4)
N_5(x) = 2x^7(21+198x-3856x^2+18982x^3-40581x^4
                    +33060x^5+12784x^6-37600x^7+17280x^8)
```

The source PDF examined for the fixtures had SHA-256
`23fc2dd648af4e835385b51b7ad5eeb0a115040203e57694abd8901332ed1e45`.
No PDF or third-party code is redistributed here. These sources establish
recurrence/fixture provenance; they are not cited as sources of the report's
explicit bivariate EGF or run-count limit laws.

## Adaptation from the frozen arithmetic audit

The companion adapts three standard-library research scripts from the frozen
3 October 2026 audit. The audit's manifest SHA-256 was
`b910c834d57c654b5792f53a8e7f32e383663c44a2b6e637b3dd3239d0ce300f`.
Their individual SHA-256 values were:

```text
check_exact_polynomials.py
59b87b72cd82c8cc243576aa7337a42fe023feff3065308c5636737c8a0a18c9

check_fixed_run_filtration.py
000fce7fba0526cc66ded1a1c24c03db9b61c1c40c3120fe48cf6356b67da0ae

certify_run_constants.py
a29351ab6b0e0b37610a2eb83008ebe1fa78c68c1041a65af9e31ff59ac33f61
```

The public adaptation:

- moves top-level calculations into import-safe, parameterized functions
- retains exact rational/integer arithmetic and explicit checks active under `-O`
- separates the EGF, primary recurrence, literal map and published fixtures
- removes file reading/writing and dependency on a saved triangle or source file
- adds bounded argument validation, JSON-only stdout, API documentation and tests
- adds the exact `rho_upper < 6/5 < log(4)` arithmetic bridge
- compares every generated complete row, optional exponential polynomial and
  ordinary numerator with the corresponding frozen audit result

The analytic conclusions are justified by the report, not by these finite checks.
The optional fixed-run denominator computation does not assert priority,
minimality of the displayed denominator, or a faster refined-count algorithm.
See the report's separate prior-art discussion for the denominator application.
