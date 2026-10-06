# Independent review of the quotient unit-pivot and companion obstruction

The explicit family and all three stated obstructions pass independent handwritten review, with no correction requested. They refute a common integral basis change that always produces a unit matrix entry, a unimodular cyclic companion basis, and a common rational triangularization for every relator quotient. They do not establish a circuit lower bound, exclude separately paid left/right transformations, or assert occurrence in the actual universal relator list. The valid three-product schedule is a total-cost tie.

## 1. The family is an actual inherited quotient

Let g>=3, p=g^2+1, h=g^2+2 and L=pg. For

    P_g=[p,g;gh,p], a=2p^2-1,

the determinant is p^2-g^2h=1. Direct multiplication of the lower, upper and lower shears with parameter g gives P_g. Also P_g=I2 modulo g. Thus the obstruction remains within the principal congruence subgroup of any specified level by choosing a multiple g>=3; this is not a claim about the fixed universal presentation's relator list.

The actual primitive right invariant is w=(1,0,-h), from w0=(2g,0,-2gh). Choose the allowed inherited basis and section

    V=[0,-1,0;h,0,1], c=[1,0,0],
    J0=[0,0;-1,0;0,1].

The cross product of the rows is -w, c*w=1, and J0 consists of the first two columns of [V;c]^-1. In particular V*J0=I2. Substituting P_g^-1=[p,-g;-gh,p] into the displayed scalar representation S gives exactly the author's matrix(4), with positive middle-row entries pgh,p^2+g^2h,pg. Multiplication by the displayed V and J0 then gives

    T_g=[a,-L;-4hL,a].                                  (1)

This hand calculation checks the minus signs and the factor4. It is not a saved coefficient-array evaluation. The identities a^2-4hL^2=1 and trace T_g=(2p)^2-2 confirm that this family satisfies the actual integral quotient and special-trace conditions.

## 2. Common basis changes and nonunit cyclic index

Since T_g=aI2 modulo L, every C in GL2(Z) satisfies C*T_g*C^-1=aI2 modulo L. Off-diagonal entries of every such conjugate are multiples of L>=30. Its diagonal entries are congruent to a. But a=-1 modulo p and a=1 modulo g. Hence a cannot be1 modulo L, since p>=10 would divide2, and cannot be-1 modulo L, since g>=3 would divide2. No conjugate has any entry equal to+1 or-1. The condition g>=3 makes the latter exclusion valid.

For any v=(x,y), independent expansion gives

    det[v,T_g*v]=L*(y^2-4h*x^2).                        (2)

Every nonzero value has absolute value at least L, and v=e2 attains L. Thus the minimum nonzero absolute determinant and the gcd of the determinant values are both L. This invariant under common unimodular conjugacy rules out a unimodular basis of the form(v,T_g*v). Moreover h lies strictly between g^2 and(g+1)^2, so the characteristic discriminant16L^2h is not a rational square. The quadratic characteristic polynomial is irreducible over Q, which rules out a common rational triangularization. Rational triangular matrices would have rational diagonal eigenvalues.

For g=3 the matrices are P=[10,3;33,10] and T=[199,-30;-1320,199]. The determinant identity199^2-30*1320=1 and scalar residue19 modulo30 both check by hand. This concrete instance already refutes the proposed uniform shortcuts; the family adds the arbitrary congruence-level conclusion.

**Review remark 1 (the unit-pivot and free-companion suggestions are refuted).** The author's numbered Remarks1 and2 correctly retain both failed suggestions. The special SL2 quotient and trace do not imply a unit entry after a common integral change of basis. For the rational cyclic basis Ccyc=[e2,T_g*e2]=[0,-L;1,a], solving Ccyc*q=e1 requires q2=-1/L. This is not multiplication by an allowed fixed integer. The input e1 is also achieved by the local signed form map: V*C0 has rows(-1,-1,0,2) and(h+2,0,1,-h-4), and the positive raw vector(1,2,h+6,2) maps to(1,0). These raw coordinates need not extend to a native or ordinary-input compiler zero; the counterexample concerns the exact all-integer action cut, where no divisibility guard was established.

Neither argument forbids independently changing the input and output bases, absorbing a conversion into a newly proved form recipe, or exploiting actual selected-word restrictions after a separate proof. Such approaches require their own integer recipe, domain and paid-consumer analysis.

## 3. The equal-diagonal rule is valid but does not lower the total

For[a,b;c,a], computing s=x+y and the products a*s,(b-a)*y,(c-a)*x, then adding the second and third products respectively to the first, gives exactly(ax+by,cx+ay). This charges3M+3A. At g=3 the fixed product coefficients199,-229,-1519 are correct. The dense schedule is4M+2A; both cost six operations.

Including the two differences from t_plus changes the core to3M+5A. Adding the existing6M+6A fully appended E_plus action gives9M+11A, still20 operations, tying10M+10A. All products by fixed signed coefficients remain paid. The author does not assert that every quotient admits this equal-diagonal form or that a runtime basis conversion is free.

**Open question 1 (unrestricted paid optimization, credited to root).** A further reduction of the current quotient append may use other integer circuits, shared consumers, charged independent factorizations or actual relator-specific structure. The present obstruction removes the three specified shortcuts and no others. It assigns no new operation total to any complete compiler and does not provide an arithmetic optimality theorem.

## 4. Provenance and execution boundary

Root posed the continuation; Pascal supplied the explicit family, exact quotient recipe and local positive-coordinate example. This reviewer independently derived the congruence, cyclic determinant, discriminant and cost identities, then read the entire author draft and requested no correction. The frozen final198-line proof and full metadata have now also been read; the final change records the independent challenge and does not alter the mathematics. The companion metadata binds the final author pair and records the exact final read scope and inherited quotient/guarded dependencies.

| Frozen artifact | SHA256 |
|---|---|
| positive7_quotient_pivot_obstruction_pascal.md | d8743949e9763dfe171b9c87b260f0feef505c4fef0bee991e548e1ca3a7ff2b |
| positive7_quotient_pivot_obstruction_pascal.json | f14a16b0cfc4188bfe9c159a414775ea6973e0d9498e8456ae2d3fce17f1cc87 |
| positive7_relator_quotient_pair_action_pascal.md | 0ddb6652ea11103bf6a5255ea233f9b1698c15b2053dcf6083d3d37b7753760f |
| review_positive7_relator_quotient_pair_action_aristotle.md | 1081d2004b7f5e139a2bbde142f76d3fb92e7cd7bbeae9ea3c67de0e0ae53e47 |

All new mathematical checks are handwritten. Only fresh byte and line metadata is computed. No supplied, saved, frozen, archived, committed or predecessor helper is run or imported; no saved source or coefficient array is evaluated, no degree propagated, and no scientific sampling, emitter or build is run. All new files are in /tmp; repository/Git and frozen predecessors remain unchanged. This is a proof-only review, with no new complete-source or external foundation audit.
