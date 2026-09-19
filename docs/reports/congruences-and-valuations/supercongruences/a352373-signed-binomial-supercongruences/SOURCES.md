# Source and status record

Consultation date: 18 September 2026 (the date of the research request).
These are bibliographical notes, not copies of the source articles.

## Selected conjecture

**OEIS A352373**, Peter Bala and contributors.
https://oeis.org/A352373
https://oeis.org/A352373/internal

The entry defines the coefficient of x^n in
`((1-x)^(-2)*(1-x^2)^(-1))^n`. Its comments state a conjectural
p^(3h) tower congruence for p >= 5 and extend the conjecture to every integer
pair r,s in the coefficient of x^n in `((1+x)^r*(1-x)^s)^n`.
The entry gives Peter Bala's author date as 14 March 2022. The internal version
consulted carries revision number 24, dated 6 January 2026. That is not used to
infer the exact posting date of each separate comment.

The general conjecture remained explicitly labelled conjectural in the entry
retrieved for this project. An OEIS page's site-wide footer timestamp is NOT
being treated as its sequence-specific last-edit date.

## Other applications

**OEIS A348410** — https://oeis.org/A348410
The coefficient of x^n in `((1-x)*(1-x^2))^(-n)`; the formulas section records
the p^(3h) tower conjecture for p >= 5. Parameters (r,s,t)=(-1,-2,1).

**OEIS A351856** — https://oeis.org/A351856
The coefficient of x^(2n) in the same power. The formulas section records the
same conjectured tower congruences. Parameters (-1,-2,2).

**OEIS A351857** — https://oeis.org/A351857
The coefficient of x^n in `((1-x)*(1-x^2))^(-2n)`, with the same conjecture.
Parameters (-2,-4,1).

**OEIS A234839** — https://oeis.org/A234839
Parameters (1,2,1). The entry explicitly corrects an earlier conjectural label:
the supercongruence was already proved in the 2014 preprint of Osburn, Sahu,
and Straub, Example 3.3. This is prior work, not a new resolution in this package.

## Primary mathematical references

**Robert Osburn, Brundaban Sahu, Armin Straub.**
*Supercongruences for sporadic sequences.*
Proceedings of the Edinburgh Mathematical Society (2) 59 (2016), no. 2,
503–518. Preprint version 2: 18 June 2014.
https://arxiv.org/abs/1312.2195v2
https://arxiv.org/html/1312.2195
https://doi.org/10.1017/S0013091515000255

Relevant locations: Lemma 2.1 (Jacobsthal valuation form), Lemma 2.4
(one-digit binomial descent), Section 2 (valuation and block-descent technique),
and Example 3.3 (the already-proved signed binomial-sum special case).

**Armin Straub.**
*Multivariate Apéry numbers and supercongruences of rational functions.*
Algebra & Number Theory 8 (2014), 1985–2008.
https://arxiv.org/abs/1401.0854v2
https://arxiv.org/html/1401.0854
https://doi.org/10.2140/ant.2014.8.1985

Lemma 5.1 supplies the classical Jacobsthal input with integer entries,
including negative upper parameters and the one-power loss at the prime 3.
The weighted block technique is standard; compare the paper's Section 5,
especially Lemmas 5.4 and 5.6. This package does not claim those techniques
as new. The explicit complementary weights for the selected coefficient
family are treated in full in the present article.

## Limits of the status check

Searches included the sequence identifiers with “supercongruence” and “proof”,
and searches for Krawtchouk/binomial convolution supercongruences. Many returned
irrelevant identifier matches; they do not establish absence of prior work.
The relevant primary papers and the OEIS entries were read directly.

No earlier proof of the complete OEIS formulation was located in this bounded
check. This is not evidence of priority sufficient for publication. The result
should be independently reviewed, and a broader bibliographic check should
precede a first-discovery claim. The paper's mathematically precise claim is
that it supplies a proof of the recorded assertion and its stated extensions.
