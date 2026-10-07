# Data sources and attribution

## Bounded sequence fixture

`data/oeis_prefix.json` contains the 35 integer values for n=0,...,34 from
OEIS A326805, as recorded on 2026-10-03. This is a small, attributed regression
fixture; it is not an OEIS export and it includes no unrelated sequences.

- Sequence: https://oeis.org/A326805
- Text record used in research: https://oeis.org/search?q=id:A326805&fmt=text
- OEIS attribution/license information: https://oeis.org/wiki/The_OEIS_End-User_License_Agreement

Credit: The Online Encyclopedia of Integer Sequences, The OEIS Foundation Inc.,
and the contributors to A326805. The
sequence's main-term conjecture was recorded by Vaclav Kotesovec on
2019-09-16. The fixture is used for bounded reproducibility and comparison,
not as an original mathematical contribution. The OEIS data are available
under the Creative Commons Attribution Share-Alike 4.0 license described
in the linked OEIS agreement; retain that attribution and applicable terms.
The checksum receipt records bytes and SHA-256 for the fixture. It is an
integrity aid, not an authenticated download receipt or digital signature.

## Literature and analytic inputs

The manuscript's bibliography credits the original sources for Abel--Plana
summation, Gamma/Stirling asymptotics, Lambert W and inversion methods, as
well as the Volterra/Ramanujan identity used for the continuous contribution.
In particular, the continuous Volterra identity and its asymptotics are prior
work; the package does not present them as a new discovery.

The source package does not redistribute third-party journal PDFs or their
extracted full text. It contains the report, independently written finite
algebra and checking code, the bounded sequence fixture, and generated exact
certificates. Raw research records and private review notes are excluded.

## Meaning of the computational evidence

- The stdlib coefficient outputs are exact rational finite algebra
- The omitted-tail certificates are exact rational inequalities
- The optional OEIS replay evaluates Gamma and powers in floating arithmetic;
  matching all fixture terms at two precisions is not an interval proof
- The optional completed-line quadrature is a consistency check with explicit
  finite cutoffs, not a certified enclosure
- The optional SymPy computation is a separate symbolic derivation of finite
  formal coefficients, not an independent proof of the analytic theorem
