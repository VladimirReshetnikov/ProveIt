# Alternative architectures and the square-carrier obstruction

This note records a research exploration, not a newly proved smaller consistency equation. It was written against the current ProveIt source collection through package 67. No endpoint improvement is claimed here.

## 1. An exact square-carrier lemma

**Lemma.** Let k >= 3 and let a be an integer with a = 1 modulo 8. There exists an odd integer y such that y^2 = a modulo 2^k. Moreover, there are cofinally many positive squares with that residue.

**Proof.** At modulus 8 take y = 1. Suppose y is an odd root modulo 2^j, j >= 3. The two integers y and y + 2^(j-1) have squares differing by

    y*2^j + 2^(2j-2) = 2^j modulo 2^(j+1).

Exactly one therefore lifts the root to modulus 2^(j+1). This inductively constructs a root modulo 2^k. For every nonnegative integer t, (y + t*2^k)^2 has the same residue and these squares are unbounded. Every step is finite elementary arithmetic, and formalizable well below ZFC. QED.

**Compiler consequence, with its necessary hypothesis.** An arbitrary finite binary payload can be put above a low suffix 001 and realized as the low bits of a square. If a proof-code compiler only inspects that finite window and already has an unconstrained high-word quotient, its code coordinate can potentially be replaced by a square. This can remove a positivity witness without restricting which payloads are represented. The high-word quotient must genuinely be free: neither existentially varying the bit bound nor appending an arbitrary variable number of symbols is by itself an ordinary polynomial construction.

## 2. Why it does not currently remove the package-64 guards

In package 64, integer41/PROOF44.md, the two guards F*alpha = Pos(...) and F*C = Pos(...) establish that F, alpha and C have a common nonzero sign, with

    q = beta*J + 1 = F + alpha + C.

This gives the absolute-radix bounds needed **before** Pell rank recovery. After the rank argument, q is proved positive and C is decoded as a complete native tableau word satisfying 0 < C < q. The latter is not merely an arbitrary residue class whose high part is discarded.

The underlying source34 coefficient proof supplies the exact support and masks. Each cell has 1,064,921 bits but only 989 permitted selector/copy/anchor/dummy positions; most positions are fixed by the native mask. There are only two specifically free Boolean dummy coordinates per cell. The canonical C has low residue 1 modulo 4; a stronger low congruence alone would not solve the issue.

An arbitrary Hensel square lift changes high bits. In this native compiler those bits still belong to cells subject to the same local mask and cyclic transport constraints. Appending sufficiently many valid halting rows provides large tableaus, but it does not prove that arbitrary prescribed high prefixes can occur. Therefore replacing C, F*alpha or F*C by a square is unjustified. A new compiler with a deliberately ignored high prefix, together with a proof that its quotient is already available, would be required.

The obstruction is to the proposed argument, not a theorem that no suitable sparse square tableau exists. That existence question has not been resolved here.

## 3. Why merely changing the computation model may not reduce the equation

The existing native compiler already maps a local accepting-tableau language into four fixed integer ports and a fixed arithmetic skeleton. Replacing K215 by a small universal machine, a finite NBG proof calculus, a tag system, or a semigroup word problem can alter those constants. It does not, without an additional argument, reduce the number of unknowns, polynomial degree or live arithmetic gates of the fixed skeleton. A small interpreter may also require a long fixed initial input, whose cost must be counted in the coefficient payload.

A promising architectural target is thus a source whose arithmetic relation is intrinsically cheaper than the current four-port mask interface, or a richer compiler invariant that eliminates a particular sign/range/rank gadget. A finite axiom count or small transition count alone is not an adequate complexity comparison.

## 4. A contemporary failure mode worth avoiding

Milan Rosko's arXiv:2510.00759 originally claimed a universal cubic equation. The current version, v8 dated 28 April 2026, is titled *Considering The Satisfiability of Cubic Diophantine Equations*. Its abstract explicitly withdraws the unbounded theoremhood-to-fixed-cubic claim. What remains is a family of bounded-resource cubic systems. The missing step is a uniform compression from all bounded slices to one fixed polynomial.

Primary source: <https://arxiv.org/abs/2510.00759> and its v8 text. This is not a reason to dismiss direct proof checking; it identifies the precise extra theorem such a route needs. Bounded tests or kernel checking of degree certificates do not supply that theorem.

## 5. Current primary background

Jonas Bayer, Marco David, Malte Haßler, Yuri Matiyasevich and Dierk Schleicher, *Diophantine equations over Z: universal bounds and parallel formalization*, arXiv:2506.20909v3, 22 October 2026, explicitly develops 11-integer universal pairs and acknowledges Sun's newer 10-integer reduction. It does not give a reduction below ten unrestricted integers. The paper separates correctness of general universality from arithmetic computations of degree and documents formalization corrections.

Primary source: <https://arxiv.org/html/2506.20909v3>.

Univariate integer equations admit a finite rational-root search, so they cannot supply the requested independent consistency statement if the surrounding consistency assumptions needed for the usual incompleteness argument hold. Quadratic solvability over all integers is decidable as well. No new general lower bound for the fixed Con(ZFC) instance is asserted here; global decidability by an arbitrary algorithm must not be silently conflated with a proof of its correctness in a particular formal theory.

## 6. Specific next research questions

1. Can the native tableau be embedded in a window of a larger code with a provably irrelevant high prefix, and can that prefix be absorbed by a transport quotient already present?
2. Can the two common-sign guards for F, alpha and C be replaced by an invariant of the accepting tableau that is provable before rank recovery?
3. Can a direct finite proof calculus yield a computational relation with fewer arithmetic ports, rather than merely smaller numerical ports?
4. Can source row combinations or source-ideal identities permit coefficient extraction with controlled collisions, replacing the requirement that every residual be separately isolated? This is distinct from changing the proof machine and seems more directly relevant to the present arithmetic bottleneck.
