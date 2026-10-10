# Corrections and clarifications

Source pin: `0efdbaa6944357e578a8839ec88d040c6e05681c`.

## 1. Pointwise differentiation is not finite-part differentiation

**Status:** proved normalization correction for an extension of the current theory, not an error found in the printed pointwise theorem.

Let `G_n` be the canonical periodic finite part of gamma_n. Then

`D^k G_n = Fp_T(gamma_n^(k)) + (-1)^(n+1) n! e_(n+1)(k) delta_0^(k)`.

Here `e_j(k)` is the elementary symmetric function of `1, 1/2, ..., 1/k`. The printed harmonic-number master identity remains correct for `x>0`. The extra term is necessary only when moving to periodic finite parts. It must not be dropped before convolution.

Concrete diagnostic: the convolution of the canonical finite parts of two trigammas is `-4 zeta'(3,x) - 2 zeta(3,x)` for `0<x<1`, not `-4 zeta'(3,x) - 6 zeta(3,x)`. The latter would result from differentiating the digamma convolution without correcting the extension of each factor. The report gives a direct absolutely convergent subtracted-integral verification of the corrected expression.

## 2. Lower-endpoint wording in the Hurwitz moment transform

**Source:** `chapters/07-integration.tex`, label `stieltjes:thm:transform`.

**Status:** localized proof clarification; the theorem is correct.

The lower boundary vanishes in the recursion with a positive power `x^m`. For the base case `m=0`, the primitive `zeta(s-1,x)` instead has equal endpoint limits when `Re(s)<1`; the two boundary values cancel and are generally nonzero.

Suggested addition:

> For `m=0`, the shift identity gives equal limits of `zeta(s-1,x)` at `x=0+` and `x=1`, so `I_0(s)=0` follows by endpoint cancellation. For `m>=1`, the lower boundary term is killed by `x^m` in the stated half-plane.

## 3. PSLQ basis wording

**Source:** `chapters/07-integration.tex`, label `integral:neg:psim2`.

**Status:** editorial refinement, consistent with the later discovery chapter.

Replace the blanket instruction that basis atoms must be Q-independent with:

> Remove known dependencies before searching, require a nonzero target coefficient, and prove any returned relation independently. A basis with unknown dependencies may still contain useful valid relations; numerical failure or basis redundancy is not an independence theorem.

## 4. Attribution and scope safeguards for the new material

The nonsingular normalized Hurwitz convolution law is already in Sun's Remark 3.2. Do not present the basic semigroup as newly discovered. The shifted-correlation specialization at zero is the classical second log-Gamma moment. Convolution powers are not pointwise powers, so the new all-power convolution formula does not solve the ordinary cubic-moment reduction problem. The current snapshot already says S4 is proved.
