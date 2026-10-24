# Scope of the shared83 and weakened86 counterexamples

Public pin: 84e16e43092614bae262ca59651cb9d77e31a255.
Review completed 2026-10-24, approximately19:48 UTC.

## Conclusion

Neither result refutes the modified complete75 compiler itself. Both refute a particular weakened arithmetic polynomial used with authentic compiler output. Neither supplies a counterexample to the unchanged source34 inputless compiler, to the full generalized signed kernel used by scalar-carrier12, or to scalar-carrier12's inherited calibration.

This conclusion concerns the applicability of these specific counterexamples. It is not a fresh end-to-end proof of source34 calibration, and it does not by itself validate an independently modified new polynomial. The new polynomial must still prove its claimed map to the full scalar12/signed-kernel interface.

## Shared-projection83: the exact deleted condition

The sound complete84 parent has

D = a*c + X + (rho+sigma)*H,
mu = a*kappa + W + rho*H,
H = 4a+3.

The shared83 candidate replaces the positive coordinate rho by a free positive U:

D = a*c + X + U + sigma*H,
mu = a*kappa + W + U.

Its forward all-ring identity is F83(U=rho*H)=F84. The inverse needs H dividing U, which is not imposed. The mathematical companion characterizes the offset:

e = X-2^R = W-2^u,
U = H*rho0-e,
H divides U iff e=0.

The later rejection theorem produces actual compiler false positives with W=0 and X=2^R-2^u. It proves such zeros at unbounded positive ordinary inputs for every original powers-of-five modified75 compiler slice, and specializes to a genuine fixed three-state machine whose language is empty. It does not assert a failure of the original compiler's tableau equivalence or of the unchanged full polynomial.

The older scout and mathematical companion still contain historical unresolved language. That status is superseded by the later rejection theorem, not evidence of inconsistent current scope.

The scalar12 interface does NOT use the free-U root replacement. It derives H|K, with K=X(X+2ac)-1, from its scalar carrier. Absolute main-Pell classification, the pre-projection rank bootstrap and a whole-product bound then prove sigma*X=2^R. It constructs d=sigma*chi_(a+2)(R) and restores the integer gamma=(d-X-ac)/H. The determinant and residue orientation then force X=2^R. Thus precisely the lost main-projection condition is recovered before native decoding. The shared83 false-positive offset sector does not survive these restored conditions.

Primary sources:
- [Exact83 coordinate change](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete83_shared_projection_scout.md), sections1–2.
- [Exact83 offset](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete83_shared_projection_math.md), section2.
- [Actual83 rejecting compiler](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete83_rejecting_compiler.md), sections1–4.
- [Scalar12 full proof](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/candidates/scalar-carrier12/PROOF.md), sections3–4.

## Weakened-bound86: a different deleted condition

This is not shared83. Its sound normalized87 parent computes

C = q-F-Z-alpha_old-2d*x,
W = C-Z,
G = q*(q-F)-Z.

The86 candidate instead computes

C = q-F-alpha-2d*x,

with the same W and G. Its exact signed identity substitutes alpha_old=alpha-Z. Completeness survives by alpha=alpha_old+Z, but positive soundness requires alpha>Z; the candidate omits that restriction. The resulting all-input-collapse theorem constructs complete positive supplied coordinates with computed C=0, R<0 and negative computed input Pell root. This is a genuine false-input family, not merely a witness-level inverse failure.

The theorem explicitly states: the sound75 certificate and87 polynomial remain unchanged. The rejecting machine is evidence that the weakened polynomial is wrong on an authentic coefficient slice, not that the compiler is wrong.

Scalar12 has no ordinary-input root loader and does not adopt the removed-Z bound. Its variables called z or T are not automatically the same variables as the universal input construction's Z or T. Its exact determinant guard is

G_det = (cone_A*F)(cone_B*C)
        -(q-cone_A*F-cone_B*C)^2 > 0.

This restores strict common signs of F,C,q and alpha=q-F-C and |q|>|F|+|C|. Together with the actual masks it yields |q|(|q|^2-1)<R<|q|^4-2 before any main projection. The C=0 and negative-R branch responsible for weakened86 is therefore excluded.

One should NOT dismiss weakened86 merely because source34 has different numerical constants: its broad parity assumptions could also hold on other numerical tuples. The decisive separation is the retained arithmetic/guard interface and its full soundness proof.

Primary sources:
- [Exact86 weakening](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_weakened_bound86_candidate.md), sections1–2.
- [86 all-input collapse](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_weakened86_all_input_collapse.md), introduction and section6.
- [Actual86 rejecting slice](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_weakened86_rejecting_compiler.md), introduction and section4.
- [Scalar12 retained signed determinant/bootstrap](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/candidates/scalar-carrier12/source/RESIDUE_AND_DETERMINANT.md), sections3–4.

## Actual scalar12 coefficient and proof ancestry

The scalar12 coefficient binding identifies tuple mixed-parity-unrounded-1064921, inherited through candidates/valuation-shared-norms/source/inherited/root_fusion/coefficients/BINDING.json. Its native ports are beta,K0,MC,MF, with MF already shifted. The two determinant constants are cone_A=2^1113 and cone_B=2^666104.

The source34 coefficient proof gives the explicit inputless native/Pell compiler:
b=121, L=8801, d=1064921, rho=2^121, B=2^1064921.
It preserves the ordered943-tile language of literal blank K215 and uses its own arbitrary-odd-factor Boolean rank controller. Its original source pin is8c6eec9d19ef80538c8e61ff6e0180040583446a. It is not the original powers-of-five ordinary-input compiler recipe appearing in the shared83 quantified theorem.

The source34 proof establishes finite coefficient recipes, exact native decoding, carry bounds, arbitrary-rotation synchronization, canonical parity and full inputless-interface transfer. Its conclusion is the ordinary formalizability chain:
fully compatible arithmetic kernel zero
iff marked periodic tiling
iff literal blank K215 halts
iff finite syntactic ZFC refutation.

The later signed determinant and residue construction consumes source64's full Q41 kernel with source34 constants. INTERPOLATION12 generalizes the strong multiplier to any nonzero multiplier and explicitly rejects an invalid odd-coordinate restoration. PRIME_TWELVE changes the root separation. Scalar12 changes the carrier and main-root extraction but restores that full generalized signed kernel before applying native/refutation calibration.

Scalar12 SOURCE_PINS.json explicitly binds:
- PRIME_TWELVE.md:5748e7a54ed8dde79130e0ae6d1db9f350bcb7cf804ec1122e1b413db375df2d
- INTERPOLATION12.md:fc6254eb1c892f7777ddd9f65207ba343586fe2fa1f373b3d4a7e61482e87da7
- RESIDUE_AND_DETERMINANT.md:92d2ab63d40028fd3eb55ec7bf0786133bc6abb3d1eb10eb296feae76d371c3f
- signed-quadratic-proof.md:dfd78f5cf75133bdfd1a260be108fcac4663e71e97ca4a85dbf36f1a0d75da4c

None of these transfers invokes the refuted shared83 or weakened86 as its sound arithmetic endpoint.

Primary sources:
- [Source34 coefficient proof](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/coefficients/COEFFICIENT_PROOF.md).
- [Source34 active coefficient binding](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/COEFFICIENT_BINDING.json).
- [Scalar12 dependency pins](https://github.com/VladimirReshetnikov/ProveIt/blob/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/candidates/scalar-carrier12/SOURCE_PINS.json).

The remaining honest boundary is the same one already stated in the report: inherited ordinary calibration and its full transitive formalization were not independently recompiled in this iteration. These counterexamples introduce no new defect in that dependency chain.
