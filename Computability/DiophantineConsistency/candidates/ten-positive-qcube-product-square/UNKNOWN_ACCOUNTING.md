# Why this kernel uses ten unknowns (heuristic accounting)

A record of the search for a nine-unknown variant, written on 24 October 2026.
This is **not** a minimality proof. It explains why every ten-positive
kernel of this family (133's product square, its q-cube normalization here,
and their parents back to 113's coprime fusion) spends exactly one unknown
on each of ten independent quantities. It also explains why dropping one
needs a new source theorem rather than a schedule edit.

| Unknown | Quantity it supplies | Why no other register can supply it |
|---|---|---|
| J, F, α | the calibration index and the two mask digits of R = [h(q − F) + α](q² − 1) + (MC + q·MF)J | fixed by the native/controller theorem; fixing α as a function of the others makes the accepted words a cyclic group (`candidates/ten-positive-scaled-norm/ONE_WORD_WINDOW.md` §2d) |
| i | the Pell period: U = i·c², with I0 a multiple of the order of [[A, Δ], [1, A]] modulo c²τ | the divisibility c² ∣ I has no polynomial witness |
| T | the auxiliary congruence V ≡ −c − R·f² (mod c·f²), through b = c(T + α) − R | the auxiliary Pell solution V is not polynomial in the other data |
| w | X = w·q = 2^R, forced by H ∣ Kpos | 2^R is not polynomial; see below |
| s | Y = q³·s, the half-binomial extraction Y = ⌊c/k⌋ read by the source reconstruction at Y(X + 1) + 2 | Y is not polynomial in c and k |
| η, ζ | the two Pell ordinates k = η + ζ (first norm E = τ²) and c = kY + η (folded strong Pell), with 0 < η < k | two independent Pell ordinates, so two unknowns; writing k = η + ζ makes the floor condition 0 < η < k free |
| n | the slack in the centre Z/M = n + κ − W·t − ρ = ε·g·y | see below |

## The exponential gadget

With H = 4A − 5, the base A acts as 5/4 modulo H. The Pell solutions for
5/4 are (5/4 + 3/4)^m = 2^m, so c = ψ_A(R) ≡ (2/3)(2^R − 2^(−R)) (mod H),
and

    Kpos = X(3c − 2X) + 2 ≡ −2(X − 2^R)(X + 2^(−R))   (mod H).

The integrality of κ = Kpos/H, together with the size bounds, forces
X = 2^R. Its five operations (3c, 2X, the difference, the product, + 2)
cannot be shared with another register, and X must be an unknown, because A
depends on X.

## The floor Y = ⌊c/k⌋

With X = 2^R, c/k ≈ (2^(R/2) + 2^(−R/2))^(R−1)/2, so Y holds the
half-binomial digits that the source reconstruction reads. Positivity of η
gives Y ≤ c/k, and ζ ≥ 1 gives Y > c/k − 1. The floor costs no unknown of
its own: η and ζ are exactly the two values c and k need anyway, and the
split k = η + ζ costs one addition. (An earlier version of this note said
ζ was spent on the floor; that was wrong, since removing ζ would leave the
Pell ordinate k without a free value.)

## The slack n

Without n the centre would have to satisfy g·y = W·t + ρ − κ exactly, with
g, y, t, ρ and κ all fixed by the canonical witnesses. Soundness needs the
transport weight L > 2gy, so W·t = (1 + hL)t > gy whenever t ≥ 1, and the
equation has no canonical zero. The candidate free parameters i and T feed
back into g, V and L, so neither can act as the slack.

## Consequence

A nine-unknown equation at kernel cost (about 80 operations) needs one of:

- a source theorem that needs only one of the two Pell ordinates c and k,
  for example one that reads the half-binomial digits from c alone or does
  not need X = 2^R and n0 = (R + 1)/2 separately;
- merging two calibration digits into one unknown under a native theorem
  that allows it.

The first item is harder than it looks. The ratio c/k is the binomial
extraction: with X = 2^R, c/k ≈ ((X + 1)/√X)^(R−1)/2, a quotient of two
exponentials in R, (X + 1)^(R−1) and X^((R−1)/2). The standard Diophantine
extractions of binomial digits (Matiyasevich, Jones) likewise use two
exponentials, u^n and (u + 1)^n. Each exponential costs a Pell ordinate, and
each Pell ordinate costs an unknown. A single-ordinate source would
therefore need a binomial extraction from one exponential. We know of none.

The binomial digits are needed because of what the native source checks.
It is a Wang-tiling encoding: 943 tiles packed into base-B digits
(B = ρ^L, ρ = 2^67), with local matching checked by masked sums against MC
and MF (`research/ten-positive-doubled-product-square/provenance/indexed_native_proof.md`).
A masked sum is a bitwise-domination test x ≼ y. Its classical Diophantine
form is Lucas's theorem: C(y, x) is odd exactly when x ≼ y. So one Pell
ordinate fewer would mean a masking test with a single exponential, which
would be a new result about Diophantine representations, not a schedule
edit. The Pell-base trick, which reads t^R from c = ψ_A(R) modulo
2tA − t² − 1, does not supply it: the denominator 2^(R(R−1)/2) of the floor
has an exponent quadratic in R, and that modulus is only about μYX².

The existing nine-positive equations (405 operations at degree 1,191,570;
`research/nine-folded-shared-odd-rank`) avoid the coefficient tuple and
compute their source inside the circuit instead, which is where the extra
operations go.
