# Proof, source, and verification audit

Date: 4 October 2026.

This audit was prepared in the same work session as the manuscript. It is
not an independent referee report or a machine-checked proof certificate.

## 1. Foundations

The main mathematics is formulated in ZFC using canonical set-coded surreal
sign sequences. Statements about arbitrary ambient formulas are schemes.
An alternative external semantics uses a specified transitive set model
of ZFC. Existence of such a model is not asserted by ZFC.

Every use of an infinite sum is set indexed. Countable sums mean formal
Hahn sums, not order-topological limits. The code's support is a set of
order type omega in decreasing order. No proper-class sum is used.

ROD permits one arbitrary real and finitely many ordinal parameters. COD
permits a countable ordinal sequence as one parameter. Naming the set R
itself does not authorize arbitrary real parameters. Conway omega^a is
not identified with exp(a log omega).

## 2. Truth and certificate check

The uniform predicates for OD(r), ROD, and COD are defined by unique-output
certificates in set structures V_theta. Reflection justifies the match to
global definitions. The extra ordinal theta is accounted for in the allowed
parameters. No global satisfaction predicate for V is introduced.

The main countable-assembly proof selects rank-local certificates using
Collection and Choice, joins all real data into a real, and flattens rank
and ordinal-parameter data into one countable ordinal sequence. The
assembly principle is applied to that ordinal sequence. Set satisfaction
then reconstructs the whole family by one formula.

No such internal uniformity assertion is made for global parameter-free
or real-only definability. These notions retain their external/schematic
interpretation.

## 3. Countable code check

For a nonnegative surreal a:

    u(a) = a/(1+a)
    e_n(a) = 2^(-n-1) + 2^(-n-2) u(a)

The band is [2^(-n-1), 3*2^(-n-2)). The upper endpoint of the next band is
strictly below the lower endpoint of the current band. Hence arbitrary
ordinal inputs, including repetitions and nonmonotone sequences, yield
strictly decreasing exponents. All exponents are positive; the leading
one is below 3/4; the resulting integer lies in (0, omega).

For the n-th exponent e, the inverse is:

    v = 2^(n+2) (e - 2^(-n-1))
    a = v/(1-v)

Normal-form uniqueness recovers the indexed exponents. The resulting
all-plus surreal recovers the original ordinal by its sign domain.
A fixed decoder thus recovers the whole sequence, not merely its range.

Finite exact checks were run successfully; data/verification.json records
the results. Their scope is only the finite rational specialization.

## 4. Completion check

COD is the classical class based on countable ordinal parameters. Its
countable-sequence closure follows from flattening countably many ordinal
parameter sequences and rank-local certificates. The minimality theorem
requires **ambient stability**: closure under every fixed parameter-free
ambient definable partial map on finite tuples, with unique output.

For a COD surreal x defined from f, the test sum Z(f) belongs to any candidate
closed class. A single fixed map decodes f and applies the particular fixed
definition of x. This proves the stated minimality. It does not prove that
field operations and countable sums alone generate all COD surreals.

## 5. Cohen-product check

The ground model satisfies V=L. Coordinate sets J are countable in that
ground model, not just countable in the extension. The ccc proof gives
countable-support names for reals and countable ground-model ordinal covers.

After a real parameter r is placed in W_J, the remaining product is weakly
homogeneous over W_J. An ordinal subset definable in the final extension
from r and finitely many ordinals therefore lies in W_J. Sign coding gives
the forward inclusion in the field classification.

For the reverse inclusion, a real g_J codes the J-generic array using a
constructible enumeration of J. Then W_J=L[g_J], and every member is OD(g_J)
in the final extension via the relative constructible well-order.

The integer-ring classification is written as intersection with the
ambient omnific predicate. The proof does not assume a blanket theorem
asserting absoluteness of all normal-form/analytic constructions across
arbitrary inner models with different real lines.

Properness uses the generic array on omega_1 times omega. Every proposed
countable support omits a coordinate whose Cohen real can be recovered
from the array, contradicting genericity over that subextension. The
same sign code has birthday exactly omega_1, while all shorter birthdays
are real-only definable. This proves the exact first omitted birthday.

## 6. Prikry check

The forcing is ordinary Prikry forcing for one fixed normal nonprincipal
kappa-complete ultrafilter. The imported classical theorem is its Prikry
property. Kappa-completeness then gives no new bounded subsets, hence no
new reals.

Cone homogeneity is proved by shrinking two tails to a common tail above
both finite stems, then replacing one stem prefix by the other while
leaving the appended sequence and tail unchanged. The induced name
isomorphism fixes ground-model check parameters. Thus a ROD subset of an
ordinal in the extension is a ground-model set, because every real
parameter is old.

To prove the cofinal sequence f is not ROD, its **graph** is coded into the
ordinal kappa*omega by kappa*n + f(n), using ordinal arithmetic. If f were
ROD, this subset would lie in the ground model and would decode there to a
cofinal function omega -> kappa, contradicting ground-model regularity.
This avoids any unjustified inference that an old set countable in an
extension was already countable in the ground model.

The omnific code then transfers non-ROD status. Each term uses only one
ordinal and a natural index and is therefore OD. The real parameters need
not vary at all. The failure is the missing whole ordinal assignment.

No equality HOD^(W[C])=W is claimed for an arbitrary measurable ground.
No optimal consistency-strength or equiconsistency claim is made.

## 7. Source separation

The pinned ProveIt report already supplies the ambient field, omnific
floor/fraction representation, fixed-parameter hereditary sign argument,
general bounded monomial code, and examples of nonuniformity. These are
credited rather than claimed as new.

The COD concept and its ordinal-sequence assembly background are classical,
explicitly present in Solovay (1970). Countable ROD assembly in the
Levy–Solovay extension is also known; the manuscript cites an explicit
statement in Kanovei–Lyubetsky, arXiv:2605.03126v1, Proposition 2.2(i).

Classical surreal references and Prikry theory are primary sources or
standard textbooks. Repository material is not treated as refereed or
Lean-verified. The current work's proposed additions are the specific
separated-band transfer, equivalence, minimality bridge, and detailed
Cohen/Prikry applications. A selective search cannot certify priority.

## 8. Actual computational and production checks

- 20,508 exact finite encode/decode checks passed.
- 206 finite sequence order/distinctness checks passed.
- 1,000 adjacent-band comparisons passed.
- Four invalid-input/endpoint tests passed.
- The LaTeX source compiled with pdfLaTeX through latexmk.
- Final PDF: 28 pages.
- All pages were rendered, contact sheets examined, and representative
  mathematical pages inspected at readable resolution.
- No overfull-box warnings or unresolved references remain. Two underfull
  bibliography lines are harmless spacing warnings.
- No Lean code was produced or built.

The proofs remain subject to independent mathematical review. The program
cannot validate set-theoretic definability, infinite ordinal arithmetic,
normal-form existence, or forcing semantics.
