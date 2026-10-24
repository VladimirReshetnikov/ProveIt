# Adversarial review: the direct and even-index sections of the final report

Review date: 24 October 2026.

## Reviewed versions

* `output/ConZFC_Carriers_and_Even_Indices_2026-10-24/report.tex`, SHA256
  `2079a51d4ede041ca0e6adf7ace78d2b037d54b5e8872521add6b547d938ca98`.
* `direct-work/delivery/even_index566/proofs/even_power_compiler.md`, SHA256
  `2f1d7404b840a8b959e38a946ed7c57748ba4075d92976eedc1bd258c06d7c26`.

The review scope is the abstract/introduction's direct-branch claims,
the bounded-interval sign combinations, the even-index argument,
simultaneous completeness, the displayed quartic, and the consistency
and verification scope. The twelve-variable carrier proof was not
re-reviewed in this task.

## Verdict

No substantive mathematical error was found in the reviewed direct/even-index
sections. The report accurately summarizes the full ordinary proof. Three
minor presentation clarifications were sent to the author; they are listed
below so that they remain reviewable rather than silently omitted.

This review is an adversarial ordinary-proof/transcription review. It does
not replace the separately supplied exact projection/coefficient checks,
and it is not a newly formalized Lean, Rocq or internal object-ZFC proof.

## Findings checked

1. **Shared-sign equivalence.** The lemma with `r+s=a+b` and `a,b>=0`
   includes zero sums and zero products. The listed final anchor uses
   the unchanged identity `x91=x94+x95+1`, so its signs are available
   before interpreting powers. The report correctly distinguishes the
   21 raw guard-witness saving from the measured 15-variable projection
   saving.
2. **Front signs and squaring.** Squaring the requested output preserves
   the meaning only because the front already supplies nonnegative m.
   The report says this explicitly and does not use m²=n^(2k) to infer
   an unsupported sign of m.
3. **Base one.** The report correctly avoids claiming that every base
   is already at least two. It identifies raw112 as a possible base-one
   case, orients each seed through the fifteen designated supporting
   calls, and then handles all remaining positive-base calls by the
   bounded congruence. This matches the finalized proof's corrected
   order and prevents the inverse-residue M*N=1 exception from being
   incorrectly discarded.
4. **Actual seed inventory.** There are fifteen distinct seed pairs and
   fifteen distinct Y factors in the common product. The report uses
   fifteen consistently. The one derived pair is separate and is not
   silently counted as another factor.
5. **Automatic lower bound.** The product identity and V>=1 exclude Y=0
   before any index identification. The parity contradiction excludes
   |Y|=1 with either sign of X,Y,S,R,U,B. Classification then gives
   |Y|>=2A>K. No removed index guard is used to prove its own replacement.
6. **Exact index recovery.** The square-divisibility extraction supplies
   |Y| dividing the common index h. The two residues imply i=+/-K modulo
   2|Y|, and the strict K<|Y| removes the minus case. The endpoint case
   in the abscissa residue lemma is included.
7. **Sign orientation.** For supporting bases n>=2 the sign table is
   correct. The frame controls both products and sums, including the
   explicit bound M+N<W+W^(W-1)<W^W. In the inverse case M*N=1 is
   impossible because N>=4. The already positive seed pair is then
   used for any n=1 call.
8. **Derived pair.** Both displayed formulas are exactly two Pell steps:
   X_(j+2)=2A(AX_j+(A²-1)Y_j)-X_j and
   Y_(j+2)=2AX_j+(2A²-1)Y_j. With the named stored coordinates, the
   emitted residuals remain quadratic. The report explicitly warns
   that the old one-step update would be invalid.
9. **Simultaneous completeness.** W is chosen from front arithmetic data
   before the auxiliary frame. The finite-ring order is taken modulo
   the whole fifteen-ordinate product. It gives odd U and positive V,
   with gcd(U,4V)=1. CRT can therefore choose one B for all seed pairs.
   The power-quotient identity is correct for all positive bases,
   including one.
10. **Witness transport.** The converse reconstructs a fresh old frame
    and old-index auxiliary witnesses. It does not incorrectly reuse
    the new doubled-index Pell tuple as an old solution. Both maps
    concern zero existence and leave the semantic front data fixed.
11. **Literal equation and scope.** The report identifies 372 explicit
    quadratic residuals in 566 unrestricted integers and their complete
    collected quartic. It attributes the source/calculus-to-refutation
    calibration to the inherited source, and distinguishes ordinary
    ZFC-formalizable reasoning from a new checked Lean/Rocq theorem.
    It makes no consistency assertion or global optimality claim.
12. **Negative control.** The n=4,k=5,m=2 example is accurately described
    as a generic arithmetic counterexample to deleting the guards
    without changing the index parity. It is not presented as a zero
    of the ZFC-source polynomial.

## Requested presentation clarifications

These do not change any equation or proof result.

* In the Pell-notation paragraph, replace “least positive norm-one unit”
  by “the fundamental unit a+sqrt(a²-1)>1”, or “the least norm-one unit
  greater than one”. Without the final qualification there is no least
  positive unit, since inverses approach zero.
* Before using a possibly negative B, explicitly extend chi_B and psi_B
  by their integer-polynomial recurrences, with
  `chi_-b(j)=(-1)^j chi_b(j)` and
  `psi_-b(j)=(-1)^(j-1) psi_b(j)` (the zero ordinate is harmless).
  The full proof already contains this, but the report's compressed
  notation initially defines the sequences only for bases a>=2.
* In completeness, make the CRT enlargement quantitative by choosing
  `B>max(A,1+4V)`. The stated nonnegative quotients then follow from
  these bounds, polynomial congruences, and monotonicity. The full
  proof already uses this concrete threshold.

The report was not edited during this review, as requested.
