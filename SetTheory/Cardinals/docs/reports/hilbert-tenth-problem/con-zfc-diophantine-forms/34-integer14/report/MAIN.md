---
title: Smaller Diophantine forms for ZFC consistency
author: OpenAI assisted research for Vladimir Reshetnikov and ProveIt
date: 23 October 2026
---

# Results and interpretation

This report combines the seven wave-4 submissions in ProveIt at commit
`8c6eec9d19ef80538c8e61ff6e0180040583446a`. It gives a small family of explicit
polynomials rather than claiming a single universal optimum. Number of
unknowns, permitted domain, total degree, arithmetic-circuit size, and
coefficient height measure different kinds of simplicity.

For every selected construction $P$ below, with the fixed coefficients and
quantifier domain stated for that construction, the conclusion is

$$\mathrm{ZFC}\vdash
 \bigl(\neg\exists\mathbf x\;P(\mathbf x)=0\bigr)
 \longleftrightarrow \mathrm{Con}(\mathrm{ZFC}).$$

This does not decide either side. The new arguments are ordinary mathematical
proofs formalizable in ZFC; they are not new Lean or Rocq certificates. The
finite audits check polynomial identities, arithmetic bounds, counts, fixed
coefficient bytes, and transcription. They do not replace the unbounded
Pell/compiler arguments or prove that the machine does not halt.

RESULTS_TABLE

The most useful concise presentation is the twelve-positive-variable form.
The nine-variable construction minimizes the natural-domain witness count
among the explicit forms considered here but pays for it with enormous
degree and some enormous coefficient recipes. The unrestricted-integer
construction serves a different purpose: its variables require no sign
restrictions. The quartic is a low-degree alternative, not a competitor on
variable count.

# Comparison with the new submissions

Packages 24--30 are mutually independent wave-4 submissions in the pinned
catalogue. Package 30 is our preceding construction. The following comparisons
use the packages' stated degree claims and independently recounted live
circuits where indicated in the accompanying review ledger.

| Package | Main contribution | Selected previous figures |
|:--|:--|:--|
| 24 | Tighter separating weights | 12 positive: degree 1069, 123 operations |
| 25 | Mixed-radix layout and external population padding | Coefficient radix $2^{5^9}$ |
| 26 | Ratio separation and parity copy tracks | 24 integers: degree 2432, 163 operations |
| 27 | Multivariate Horner evaluation and exact coefficient aliases | Nine positive: 1537 operations |
| 28 | Signed-divisor finalizer | Nine nonnegative: degree $93264\cdot5^{33}+288$ |
| 29 | Coprime Pell guards and intersective divisibility | 17 integers, 20607 operations |
| 30 | Quartic register elimination and scalar norm evaluation | 12 positive: 111 operations; positive quartic in 31 variables |

The new combinations are structural, not mere relabellings. They reuse
package 27's exact coefficient-expression aliases after reducing the Jones
parent to 31 variables; improve the signed majorants in package 28; replace
the positivity mechanism used by package 29; and translate the carrier in
package 30's inexpensive norm. The fixed compiler tuple is rebuilt coherently
from the smaller-layout ideas, not assembled by mixing ports from different
submissions.

No construction here is claimed to beat the inherited 67-operation single
polynomial or 59-operation system on operation count alone. Those remain
useful alternatives. A system whose equality comparisons are free is not
directly comparable to a single-polynomial residual circuit.

# Conventions and proof dependencies

We write $\mathbb N_0=\{0,1,2,\ldots\}$ and
$\mathbb Z_{>0}=\{1,2,\ldots\}$. All quantified variables are listed; every
other named expression is either an abbreviation or a fixed integer
coefficient. An arithmetic circuit uses only binary addition, subtraction,
and multiplication. Multiplication by a fixed numeral counts as a gate.
Shared subexpressions count once. Construction of fixed coefficients is not
included in the evaluation-gate count, and is documented separately.

The common proof chain is:

1. The fixed blank-tape run of K215 halts exactly when the specified syntactic
   ZFC proof system has a finite refutation.
2. The finite native tile language and its no-carry compiler describe exactly
   those halting runs.
3. The Pell arithmetic interface represents the compiler conditions.
4. The new polynomial transformations preserve existence of solutions in
   the explicitly stated domains.

The first three steps are inherited mathematical dependencies, with pinned
source proofs supplied or identified in the archive. The fourth step and the
new compiler-parameter adapter are proved here. The ZFC-provability claim is
obtained by formalizing the arithmetic arguments within ZFC, not by invoking
Lean's or Rocq's soundness inside ZFC.

Every arithmetic instance uses the same four ports
$\beta=B-1$, $K_0$, $M_C$, and $M_F$, where $M_F$ is the shifted source mask,
not the native high mask. Whole-tuple bindings are mandatory. A smaller
radix does not reduce the Jones parent-variable count $\nu$; that count is
31 because of the separate quartic reduction.

# How the smaller fixed coefficients are constructed

COEFFICIENT_SUMMARY

# A lower degree twelve variable norm

POSITIVE_SUMMARY

# A quartic in fifty unrestricted integers

The previous signed lift has 51 integer coordinates and 30 quadratic
residuals. Its only use of a packing register $G$ is

$$G=q(q-F)-C,\qquad
k-1-hE=LG+(M_C+qM_F)J,$$

where $q=\beta J+1$, $C=q-F-\alpha$, and the retained equations include
$L=q^2-1$ and $N=q(L+1)$. Delete $G$ and replace the packing equation by

$$k-1-hE=(q-F)(N-q)-CL+(M_C+qM_F)J.$$

It is still quadratic. The polynomial identity

$$L[q(q-F)-C]-[(q-F)(N-q)-CL]
  =(q-F)[q(L+1)-N]$$

proves an exact bijection of the integer zero sets: forget $G$ in one
direction, and restore $G=q(q-F)-C$ in the other. Unlike the positive-domain
version, no positivity proof for this restored register is needed.

The other 28 residuals, including all six positivity guards and the odd
scale, remain unchanged. Hence this reduction inherits exactly the source's
signed-domain soundness theorem. Taking the sum of the 29 squared residuals
gives a quartic in 50 unrestricted integers. Its coefficient of $\tau^4$ is
1, so its degree is exactly four for every admissible coefficient tuple.
The archive contains all residuals, a symbolic identity check, and a separate
independent reconstruction audit.

# Nine natural variables with a smaller signed finalizer

The local majorant MF below is unrelated to the fixed compiler mask port.

NINE_SUMMARY

# Fourteen unrestricted integers

SIGNED_SUMMARY

# Verification and reproducibility

The archive records a pinned source ledger and exact arithmetic circuits.
Its root verifier first checks immutable file hashes, then runs the new
checks in a temporary copy. Source programs received from the repository
are preserved as inert text or data; no received program is executed by the
release verifier. The archive includes the symbolic identities and full
proof text rather than presenting random evaluation as proof.

VERIFICATION_SUMMARY

A positive computational result here means that the stated finite check
passed. It is not a successful search for a solution of the Con(ZFC)
equation. There is no such search or witness claimed in this report.

# Further research questions

1. Can the remaining signed Pell guards be reduced without restricting the
   Jones ratio witnesses to a family lacking a completeness theorem?
2. Can a general formal theorem expose the cofinal choice of Jones radix,
   so that square-scaled substitutions no longer require inspection of the
   existing completeness proof?
3. Can the carrier translations be optimized systematically, with a symbolic
   valuation certificate tracking every radical branch and its cancellation?
4. Can another quartic register be eliminated by an identity modulo retained
   equations, rather than by direct substitution that raises degree?
5. Can the new exact coefficient layout and actual-rank controller be
   formalized once as a reusable compiler interface?
6. Can coefficient expressions be reduced further without concealing their
   materialization cost or changing the meaning of the operation metric?
7. Can an explicit instantiation of a smaller unrestricted-integer universal
   representation improve this archive's count while retaining a complete
   coefficient recipe and a manageable proof?

# Sources attribution and limitations

The primary source is the pinned ProveIt catalogue and its packages 24--30:

<https://github.com/VladimirReshetnikov/ProveIt/tree/8c6eec9d19ef80538c8e61ff6e0180040583446a/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms>

The source ledgers identify exact files and Git blob hashes. The mathematical
contributions of the earlier packages, Jones's reduction, the K215
construction, and the compiler ancestry remain credited in the retained
notices. This report and its newly authored checks are OpenAI-assisted
research prepared for Vladimir Reshetnikov's ProveIt project. Independent
audits described here are separate checks within that collaboration, not
external human endorsements.

New material follows ProveIt's MIT No Attribution terms. Inherited third-party
material retains its own licence; the Wade licence and K215 attribution notice
are included. Historical source notices may name paths in their original
packages. The active release paths and coefficient bindings are defined by
the root README and binding manifests, not by those historical references.

Sun's 2026 preprint states in Theorem 1.1 a representation of every recursively
enumerable subset of the natural numbers using ten unrestricted integer
witnesses. This prevents any interpretation of our count as a global
fewest-variable record. Our contribution is an explicitly instantiated
polynomial with a fixed coefficient recipe and a detailed dependency chain;
we have not instantiated Sun's general construction for the particular
ZFC-refutation predicate. See <https://arxiv.org/html/2609.01594v2> and the
archive's scope note for the exact distinction. We have not independently
audited the complete proof of that external preprint.

There is no global minimality theorem, proof of Con(ZFC), new kernel-checked
end-to-end result, or claim that every large fixed numeral is materialized.
