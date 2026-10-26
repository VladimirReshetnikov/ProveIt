# Independent review of the CRT-anchor / joint-certificate composition

This is an internal AI-assisted mathematical and finite-algebra review. It
does not constitute external peer review or a newly compiled proof-assistant
development. The reviewed source boundary is ProveIt commit
`ecb9a4b4dda617512952525d50f17343700aac52`.

## Conclusion

The new 209-variable bridge is sound and complete relative to the explicitly
identified package173 arithmetic/refutation calibration. Combining the
encoded-index anchor of173 with the simultaneous orientation-and-power theorem
of176 is valid. No premise of that joint theorem requires canonical pair
orientation before the joint certificate proves it. The new proof correctly
uses bounded *classified* indices at that stage.

The change permits the advertised subsequent exact monic substitutions. This
review checks the semantic interface; the independent projection checker has
the separate responsibility for the selected85-variable literal graph and
its exact degree16964 certificate. This note does not independently claim to
have reconstructed that complete projection or its degree ray.

## Literal finite interface checked separately

`check_joint_interface_full.py` imports neither the construction producer nor the
projection search. It expands the relevant graph ports as sparse integer
polynomials in the original219 coordinates and checks:

1. There are exactly16 power requests and14 unique principal Pell pairs.
2. With A=x137+1, source row147 is exactly

       Omega - (A-1)*x204 - sum(the14 retained principal norm residuals).

   The source norm rows, in zero-based order, are
   101,109,111,113,115,117,119,121,123,125,127,129,131,133.
3. Let S be the set of33 distinct actual polynomial atoms appearing as
   a requested base, requested index, or requested output. The retained
   frame row134 gives the exact identity

       W = 1 + sum_(a in S) a^2 + 2(t^2+t+1).

   Since t^2+t+1 is strictly positive for every integer t, every actual
   atom satisfies a^2<W. In particular the new affine index2^20*t is
   included. This is an algebraic check of the actual index expression,
   not an inference from its label.

4. All sixteen hardcoded request ports agree with the actual graph. Every
   retained multiplication wire and centered principal norm has its stated
   coordinate interpretation, including the two shifted coordinates.
5. The three singleton modulus and quotient pairs, and the two same-base
   aggregate pairs, agree exactly with their old private residuals. The
   signed squared-error identity is checked modulo the exact retained
   multiplication wires, rather than assuming those wires implicitly.
6. The complete emitted joint residual agrees coefficient by coefficient
   with the independently constructed mathematical formula. It has 66,371
   collected monomials and exact degree 13. Its squared sum with the other
   quadratic residuals consequently has exact degree 26.

The full receipt is `joint_interface_full_receipt.json`. All equalities are
exact coefficient comparisons, not random-point tests. The checker accepts
an explicit `--component-root` for use in the final package and uses only
the Python standard library.

## Unbounded arithmetic audit

The retained horizon gives t>=16. The frame and odd-Pell construction give
W>=258 and |A|>W^W. Package173's encoded-C anchor identifies the anchor's
positive classified index as |C|, with C nonzero, using only its comparison
congruences and squared-ordinate bound. None of the11 deleted rows is used.
The bound on the other raw classified indices follows from the same
squared-ordinate inequality. This supplies the premise needed by the176
joint theorem before the old orientation row has been recovered.

Write b=floor(sqrt(W-1)); then b>=16. Each raw pair is
epsilon_i*(X_nu_i(A),Y_nu_i(A)), with epsilon_i=+1 or-1 and |nu_i|<=b.
The signed recurrence modulo A-1 yields the nonnegative error

    o=sum((epsilon_i-1)^2+(epsilon_i*nu_i-k_i)^2).

This formula covers zero classified indices and both signs of the
abscissa. The bound o<=120b^2 is conservative for14 pairs.

At a nonzero base n, T=2An-n^2-1 is nonzero, gcd(n,T)=1, |T|>W^W,
and n/T has the sign of A. These follow from |n|<=b and |A|>W^W.
The modular Pell identity for a negative classified index is valid because
n is invertible modulo T. Multiplying all active errors by
Cstar=product(n_j^b) makes every exponent and numerator integral.

After division by the nonzero denominator product, the new residual says
that a sum of rational errors is an integer. Replacing each numerator
by its congruent bounded numerator preserves integrality separately;
no pairwise coprimality between denominators is needed. The resulting sum
is

    Cstar^2*o/(A-1) + sum(n_j*d_i^2/T_j).

Every nonzero summand has the sign of A. There are at most5 active bases,
14 pairs and16 requests, so the inherited17-request bounds remain valid:

    Cstar^2*o+sum(|n_j|*d_i^2)
      <=188b^(12b+2)<W^(6b+2)<=W^W.

The inequalities use188<W, b^2<W, and6b+2<=b^2+1<=W for b>=16.
Thus the sum is an integer of absolute value below one and must vanish.
Common signs force o=0 and every active d_i=0, giving canonical pair
orientation and the requested exact signed-index powers simultaneously.

## Restoration can precede semantic sign recovery

There is a useful simplification of the main proof. For a nonzero base,
the just-proved exact power identity implies T divides its error delta.
For a zero base, T=-1, so the same divisibility is automatic. Consequently
every deleted singleton modulus and quotient can be restored immediately:

    T=2An-n^2-1, quotient=-delta/T.

For each deleted same-base aggregate, the identity

    E=sum(delta_i^2)+T*sum(Y_i^2)

makes L=E/T integral at nonzero bases, and at a zero base the denominator
is again-1. Then K=2H+(2A-n)L restores both original aggregate rows.
Canonical pair congruences make Omega/(A-1) integral and restore the old
orientation quotient. The checked row identity accounts for its changed
coordinate form exactly.

This produces a zero of the frozen219-variable parent without first
needing to reproduce its nonzero-radix bootstrap. The parent calibration
then recovers the finite refutation. Conversely any parent zero has its
canonical pairs and exact powers; the sum of the old quotients defines
the new integer z. Hence the209-variable system and the parent are
equisatisfiable over unrestricted integers.

Restoration is only asserted on zero sets. It uses rational expressions
whose denominators have been proved nonzero and whose values have been
proved integral. It is not a global polynomial identity on all tuples.
The subsequent unit-pivot stage does provide a global integer-polynomial
restoration and exact pullback identity; the two claims must remain distinct.

## Label-growth boundary

The affine parent uses K=2^20*t. Its validity requires the refined
package173 lemma in `LABEL_SEPARATION_WITHOUT_DERIVED_RANGE.md`, which
allows F=L^t. One must not substitute the older sufficient condition
D>d+1 from an earlier paragraph of `C_ANCHOR_THEOREM.md`.

The refined proof is correct: first recover equal factor counts m<=t.
Both degree-m product polynomials have positive coefficients in every
degree0 throughm. Their coefficients are at most L^m<=F, so the
difference coefficients are strictly between-F andF even at the
endpointF=L^t. Reduction modulo F then proves polynomial equality.

## Scope

These checks support the new ordinary mathematical bridge, with the
named inherited C222/ZF and ZF/ZFC logical equivalences. They establish
neither an actual Diophantine zero nor absence of zeros, and do not
assume consistency. They do not claim worldwide novelty, global
minimality, or a fresh compilation of the complete historical proof
closure. Exact coefficient architecture, variable domain and degree
must remain part of each comparison.
