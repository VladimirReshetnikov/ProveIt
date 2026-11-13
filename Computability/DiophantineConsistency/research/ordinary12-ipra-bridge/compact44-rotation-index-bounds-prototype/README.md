# Exploratory bounded rotation indices

`RotationIndexBounds` proves internal quotient bounds for both non-wrapped and wrapped source positions, bounds an exponent reduced modulo `67*n`, and proves that for a bounded word X the next digit after q<n is either still inside n or is the zero digit at q+1=n. `RotationCoverageBounded` strengthens the three-case partition: if k<n and e<67*n, each case has q<n and r<67; its genuine straddling case additionally has 0<a<67, while the a=0 boundary is treated as non-wrapping.

`RotationBoundedCases.reduced_digit` composes the previous model rotation identities for the exponent `E % (67*n)`. Given only k<n and `X<2^(67*n)`, it returns model q<n and r<67, the next-digit in-range-or-zero condition, and either the two-adjacent-digit formula or the explicit straddling-splice formula. The q+1=n digit is zero padding; it is not asserted equal to the first digit. The result is existential and its witnesses have not been selected from graph positions.

Author-only compiler sessions 95044, 27989 and 93343 actually exited 0, without warnings or `sorryAx`; the named reports use `propext`, `Classical.choice`, `Quot.sound`. Session 65963 actually exited 1 on tactic sequencing; its source and log are retained and its `sorryAx` report proves nothing. The author overlay and dependencies from the coverage packet a09b6d055b were used. This is exploratory evidence, not a paired replay or independent artifact audit.

No strict half-radix bound, clean predecessor, graph-column decoding, retained-K binding or internal iPRA conclusion is claimed.
