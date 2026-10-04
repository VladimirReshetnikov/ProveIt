# Exact degree and a paid single-polynomial form

This separate addendum preserves the previously frozen digit-dilation packet unchanged. It concerns only that raw recoder. In particular, C (or G) is a free degree-one input: substituting the periodic-board expression G=W^576000 is outside this degree statement.

Give degree one to every free input and every positive witness of the frozen arithmetic DAG, and degree zero to its fixed numerals. For each asserted equality L_i=R_i, let f_i=L_i-R_i be its ordinary integer-polynomial residual.

**Exact-degree theorem.** Each of the six frozen modes (EXP, forward, reverse, pair, inline pair, positive-port pair) has max_i deg(f_i)=6. The direct single polynomial F=sum_i f_i^2 has exact total degree12 and satisfies F=0 if and only if all the original equations hold. This introduces no further witnesses and makes no minimal-degree or optimal-operation assertion.

Proof. All arithmetic in a power macro has degree at most4 except its growth-Pell residual. Macro bases are constants or degree-one expressions; its only possibly quadratic exponent argument is CP+2, which enters linearly into k and the relevant equations. The growth residual is

a^2-1-((w+1)^2-1)(wg)^2 = a^2-1-w^4g^2-2w^3g^2.

Here a is affine in a dedicated positive witness. Thus the unique degree-six monomial is -w^4g^2, and every macro contains one such residual. Outside the macros, coefficient extraction, reversed residue extraction and tape assembly have degree at most3. This proves both the upper bound and the exact degree-six lower bound.

The homogeneous degree-twelve part of F is precisely the sum of w^8g^4 over the separate growth-Pell equations. Their witness pairs are distinct; every coefficient is+1. Consequently cancellation is impossible and deg(F)=12. Finally, an integer sum of squares vanishes exactly when every squared residual vanishes.

There is one degree-six residual for EXP, seven for each one-word recoder, and fourteen for each pair mode. The names g in this proof appear as the private z-suffixed witnesses in the literal DAG.

## Literal, deliberately naive SOS ledger

For E equations, form every residual with one subtraction, square it with one multiplication, and add the E squares with E-1 additions. The additional cost is E M+(2E-1) A=3E-1 operations. Arithmetic intermediates remain expressions; no new existential variable is needed.

- EXP: E=15; add44 operations; total114=46 M+68 A;25 positive witnesses
- Forward word: E=114; add341; total865=338 M+527 A;196 positive witnesses
- Reverse word: E=114; add341; total868=341 M+527 A;196 positive witnesses
- Inline pair: E=228; add683; total1738=682 M+1056 A;392 positive witnesses
- Separate-port pair: E=231; add692; total1747=685 M+1062 A;392 internal positive witnesses
- Positive-port pair: E=231; add692; total1748=685 M+1063 A;392 internal positive witnesses

The inline outputs A and T are expressions; B aliases an existing positive witness. In the separate-port variant A,B are positive ports and T is nonnegative. The positive-port variant exposes Tplus=T+1. The internal witness counts do not count separately quantified external ports; quantifying A,B,Tplus adds3 positive variables. Consuming Tplus-1 may require its separate adapter operation as already documented in the core proof. No interface change is hidden in these ledgers.

These counts use the frozen free-fixed-numeral convention. If only literal1 andliteral3 are free, the shared constructions2=1+1 and4=3+1 add2 A to each standalone mode; they change neither the degree nor the number of witnesses. Reuse of constants supplied by another component must be recorded separately.

## Independent data-only verification

check_degree.py reads the six literal final-evidence/*-dag.json files and first authenticates their frozen whole-file SHA256 hashes. It does not import or execute the core DAG builder or any upstream code. It constructs exact sparse integer polynomials for every arithmetic node, expands and collects every residual, and expands and collects the complete SOS. All tests use explicit guarded exceptions and remain active under optimized Python.

Both normal and python -O runs reproduce degree_receipt.json. The inline pair has exactly1877 nonzero monomials after collecting the expanded SOS; its degree12 part has exactly14 monomials, each w^8g^4 with coefficient1. The separate-port pair has1892 collected monomials and the same14 top-degree terms. These term counts are secondary checks on the specific literal DAG, not claims that the expanded polynomial or its circuit is sparse-optimal.

The authoritative core remains /workspace/shared/fixed-digit-dilation-20261003/final-evidence/. This addendum's checker is read-only and prints its receipt to stdout; redirection creates only the separately chosen result file. No frozen core file was changed.
