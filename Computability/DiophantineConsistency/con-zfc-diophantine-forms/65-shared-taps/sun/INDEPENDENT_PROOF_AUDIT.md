# Independent internal review of the ten-integer companion

The review was carried out by a separate mathematical agent during this
AI-assisted research session. It is not external human peer review or a
proof-assistant kernel certificate.

## Circuit and degree

The reviewer independently parsed `generated/sun10.json`, authenticated the
four compressed coefficient payloads and their raw hashes, checked dependency
order and liveness, and obtained 337 multiplications, 161 additions, and
27 subtractions: **525 live operations** on **ten integer variables**.

The exact degree is **7,428,120**. Independent leading-coefficient propagation
with the actual fixed ports gives residues 95, 646, and 515853 modulo 101,
1009, and 1000003, respectively. The review also derived the positive analytic
certificate now included in the paper:

\[
[t^{7428120}]F_{10}(t,\ldots,t)
 =2^{7957040919272}3^{7426392}>0.
\]

The unique dominant term of the final norm is the fourth power of the
scaled radicand \(A_2\), which has degree 1,857,030. The subtracted term
has strictly smaller degree. The supplied verifier checks the literal
degree propagation and its agreement with the analytic certificate.

## Signed bootstrap

The reviewed proof uses the following implications in order:

1. The intersective quintic makes the numerator nonzero. A zero of the final
   norm therefore has nonzero denominator, so the positivity witness is nonzero.
2. Structural square-class separation applies before source positivity;
   the needed strict bound on the first radicand follows from its explicit
   formula. All three unscaled radicands must be integer squares.
3. The coprime factors of the first radicand and the congruence of the source
   base modulo 3 force the base to be a positive square. The case of base 1
   is impossible, so the base is at least 4.
4. The second factor of that radicand forces the positivity expression to
   be positive, and hence the approximation margin is positive.
5. The margin formula then forces a positive packed coordinate and the
   strict upper bound twice the source cap. These estimates hold before
   the source polynomial positivity and block-range bounds are invoked.
6. The inherited arithmetic bridge recovers a binary base and the binomial
   divisibility. The exact new coefficient identities then recover the source.

No circular assumption about source positivity or the packed-coordinate
range was found. The new kernel degree gaps 18 and 489 supply the required
source positivity after this bootstrap. The inherited compiler and Sun
arithmetic theorems remain explicit dependencies of the complete statement.
