# A quartic in 50 unrestricted integers

This construction combines the signed odd-scale lift of wave-4 package 29
with the packing-register elimination of package 30. It improves the
51-integer quartic to 50 integers without increasing its degree. There are
29 quadratic residuals, so the corresponding system has maximum degree 2.
The exact residuals are in `quartic50.json`.

## Algebraic equivalence

Write q=beta J+1 and C=q-F-alpha. The source retains the equations

    L=q^2-1, N=q(L+1), G=q(q-F)-C,
    eta+zeta-1-hE = LG+(MC+q MF)J.

Delete G and its defining equation. Replace the last right-hand side by

    (q-F)(N-q)-CL+(MC+q MF)J.

This remains quadratic in the retained unknowns because q and C are affine.
The identity

    L[q(q-F)-C] - [(q-F)(N-q)-CL]
      = (q-F)[q(L+1)-N]

proves equivalence whenever the unchanged N equation holds. Forgetting G
maps every source solution to a new solution. Conversely, restore the integer
G=q(q-F)-C. All original equations then hold, and this restoration is unique.
Thus there is an exact bijection between the two integer zero sets. No sign
argument or extra divisibility assumption is needed: G is unrestricted.

The other 28 residuals are unchanged, including all six positive guards,
the odd scale, odd auxiliary multiplier, square power scale, and exposed
quotient equations. Consequently the source's soundness and completeness
theorem applies with precisely its existing coefficient tuple. In particular,
the exposed-quotient argument and exclusion of negative scale are neither
weakened nor replaced by experimental testing.

## Fixed coefficients and logical conclusion

The initial binding is the complete compact943 tuple from the source:
beta=B-1, K0=K, MC, and shifted MF=MF_source, with B=2^(5^10).
The inherited coefficient manifest is provenance; the release must supply
an explicit binding to its payloads. Any transfer to a different complete
tuple requires the same source-interface theorem, not componentwise mixing.

The algebraic equivalence above is valid for every integer tuple of ports.
With the authenticated compiler tuple, composing it with the signed
Pell/compiler theorem and K215 calibration yields, within ZFC:

    no integer solution of quartic50 = 0 iff Con(ZFC).

Here quartic50 is the sum of the squares of the 29 displayed residuals.
Its degree is exactly four, not merely at most four: tau occurs in exactly
one residual, with term tau^2, and the coefficient of tau^4 in the sum is 1.
The normalized polynomial has 362 expanded monomials when the four ports
are treated as coefficient symbols. No global optimality or new proof-assistant
certificate is claimed.

## Reproducibility and attribution

`build_quartic50.py` is newly authored and uses SymPy to verify the exact
packing identity, unchanged residuals, variable liveness, degree, and the
coefficient of tau^4. It reads the pinned source JSON as data and does not
execute any upstream program. These checks verify the algebraic reduction;
the unbounded compiler/consistency equivalence is the mathematical argument
above and the cited inherited theorem.

Source pin: 8c6eec9d19ef80538c8e61ff6e0180040583446a, ProveIt,
SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms,
29-simpler-forms/low_degree/generated/integer51_degree4_odd_scale.json.
The source proof is included as upstream/ODD_SCALE_LIFTS_PROOF.md.
The register identity is from package30/arithmetic/QUARTIC31_PROOF.md.
This is AI-assisted mathematical synthesis for ProveIt.
