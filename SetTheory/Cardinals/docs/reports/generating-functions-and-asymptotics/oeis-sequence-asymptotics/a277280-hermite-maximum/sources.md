# Sources and provenance

Consulted on 20 September 2026.

1. OEIS A277280, introduced by Vladimir Reshetnikov on 8 October 2016.
   https://oeis.org/search?q=id:A277280&fmt=text
   https://oeis.org/A277280
   The consulted text entry identified its revision timestamp as
   28 June 2026, 15:48:14. Its definition retains coefficient signs and its
   n=5 example gives 120, not 160. The 25 displayed terms were transcribed
   into the finite verification script. The entry credits Vaclav Kotesovec
   for the b-file and the consecutive-ratio plot.

2. NIST Digital Library of Mathematical Functions, equation 18.5.13.
   https://dlmf.nist.gov/18.5.E13
   Used for the physicists' Hermite-polynomial coefficient formula.

3. NIST Digital Library of Mathematical Functions, Section 5.11.
   https://dlmf.nist.gov/5.11
   Used for Stirling's expansion and the real-positive alternating remainder
   bound in Section 5.11(ii).

4. OEIS A277281.
   https://oeis.org/A277281
   The comparison sequence takes coefficient magnitudes rather than signs.

## Numerical-data provenance

The full b-file is linked by OEIS at
https://oeis.org/A277280/b277280.txt . It was accessible through the web
reader, but a direct download into the computational runtime did not succeed.
The full file was therefore **not** part of the executed numerical comparison.
The supplied optional `--oeis-file` check accepts a separately obtained copy.

The computed b-file in this archive was generated from the exact streaming
recurrence proved in the article. The CSV and all three figures were computed
locally from the article's formulas. They are not copied OEIS graphics.

The exact maximization, asymptotic coefficients, and fluctuation statements
are supported by the article's own proofs. Citations to the above references
identify the standard starting formulas and sequence definitions; they are
not claims that those sources already contain the new derivations in this
note. Historical priority has not been established.
