# Reconciliation of the three Diophantine manuscripts

This record covers the elementary algebra in Sections 1–4 of the maintained
[article](article.tex). It does **not** certify integration of every result
in the three manuscripts or review of the base text's later proofs.

## Recoverable sources

The original ZIP files are tracked at commit `f0b7f43` under `docs/new/`.
Commit `be06fc8` placed their supplementary files here and installed source 01
as the article, without merging the other two texts.

| Source | Archive | TeX member |
|---|---|---|
| 01 | `omnific_integers.zip` | `omnific_integers/omnific_integers.tex` |
| 02 | `omnific_integers_diophantine.zip` | `omnific_integers_diophantine/article.tex` |
| 05 | `omnific_integers_article.zip` | `omnific_integers/article.tex` |

The source-01 extraction was byte-identical to the installed base before
this review. All its 41 standard theorem/lemma/proposition/corollary
statements are retained. Their labels, and the article's other labels, now
have the report prefix `odg:`; the suffix is unchanged. Four new standard
statements bring the count to 45. Proof and explanatory changes in this pass
are confined to Sections 1–4; label/reference renaming applies throughout.

## Elementary algebra correspondence

The labels in the source columns are local to those archived manuscripts.
The maintained labels resolve in [article.tex](article.tex).

| Topic | Companion source | Maintained location and disposition |
|---|---|---|
| Rings and constant-term retraction | 02 `prop:ring`, `thm:augmentation`; 05 `thm:retraction` | `odg:prop:ring`; retain the base proof and distinguish the complex kernel `J + iJ` from `J`. |
| Degree, units, finite elements and floor | 02 `lem:units`, `prop:finite`, `thm:floor`; 05 `lem:degree`, `cor:units-B`, `prop:discrete`, `prop:floor` | `odg:lem:degree`, `odg:prop:units`, and `odg:thm:floor`, with the base's intervening discrete-order argument; agree on growth-support conventions. |
| Local Hahn workspace | 05 `lem:workspace` | New `odg:lem:workspace`; the rational span of the support union contains the input family. Later global bounds may require enlargement. |
| Ordered remainder | 02 `cor:division`; 05 `cor:division` | `odg:prop:division`; ordered division does not imply Euclidean termination. |
| Ordinary divisibility and residues | 02 `thm:congruences`; 05 `thm:divisibility` | `odg:thm:finitequotients`; depends on every support exponent being nonnegative. |
| Mixed gcd and ordinary primes | 02 `cor:mixedgcd`; 05 `cor:ordinary-primes` | New `odg:cor:mixedgcd`; `(n,x) = gcd(n,ct(x)) A` for nonzero ordinary `n`. |
| Positive-characteristic quotients and completions | 02 `thm:finitequotients` and its following completion corollary; 05 `prop:finitequotients` | `odg:cor:charideals` and following prose; inverse systems use ordinary residue rings, not sets of proper-class cosets. |
| Common divisor and idempotent kernel | 02 Section 5; 05 `lem:set-bounds`, `thm:common-divisor`, `cor:idempotent-ideal` | `odg:lem:setbounds`, `odg:thm:commondivisor`, `odg:cor:Jglobal`; retain the stronger base conclusion that no set generates `J`. Add the consequences `J/J² = 0` and `J`-adic completion `ℤ`. |
| Nilpotent-image test | 02 `cor:nilpotent` | New `odg:cor:nilpotent`; the image need not be an ideal of the whole target. |
| Clearing and common multiples | 02 Section 5 and `cor:commonmultiples`; 05 `thm:fractions` | `odg:thm:fractions` and new `odg:cor:commonmultiples`; one monomial clears every ordinary power of a set-sized family. |
| Failure of integral closure | 05 `cor:not-integrally-closed` | Add its shorter witness `√2 = (√2 ω)/ω` after `odg:prop:notnormal`; retain source 01's nonconstant witness `√(ω²+1)`. |

The additions are direct support, divisibility and ideal arguments. The
review also makes explicit that constant coefficient is not order preserving
and differs from standard part; `v = −deg` translates growth exponents to
valuation exponents. Quotients by class ideals are interpreted through their
congruence maps and ordinary representatives where available.

## Remaining reconciliation

The comparison read source 02's Sections 2–5 and source 05's elementary
normal-form, integer-part, residue and global-support arguments through
its integral-closure corollary. This is not a claim that every assertion in
those portions has been copied: for example, their separately stated CRT,
prime-adic order and univariate consequences still need an explicit
correspondence with the complete base text.

Source 01's Sections 5 onward, including equational transfer, rigidity,
quadratic classification, the quartic guard, primitive points and later
formalization discussion, retain their original proofs. Their comparison
with the remaining source-02 and source-05 claims, including polynomial
lifting, differential/Wronskian methods and set-target rigidity, is pending.
The [set-sized quotient report](../set-sized-quotients-of-omnific-integers/)
contains related material and needs its own eight-source reconciliation.
Imported normal-form foundations, classical results and historical priority
remain separate review obligations.

The three preserved verification scripts exercise ordinary finite examples
from their respective sources. They do not prove the new class-sized
support arguments or establish full equivalence of the three manuscripts.
No additional Lean theorem is asserted by this reconciliation.
