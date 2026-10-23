# Native arithmetic and the remaining calibration contract

The package-52 checkpoint's coefficient tuple is
`wang943-complement67-shared-anchor-length8807-prime581197`, pinned to
`124c07c0b77a9e20e84676514d8b1ff78536ea3f`. Its four ports are the complete tuple
`beta,K,MC,MF_source`; the fourth port already includes the shift by `B-1`.
The binding is in
[COEFFICIENT_BINDING.json](con-zfc-diophantine-forms/52-sparse-pell/coefficients/COEFFICIENT_BINDING.json).
It binds the same 31-positive-variable, 22-equation source whose SHA256 is
`ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48`.

[NativeArithmetic52.lean](Lean/DiophantineConsistency/NativeArithmetic52.lean)
eliminates its fifteen lifting coordinates by explicit arithmetic. For the
remaining sixteen coordinates

```
J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma,
```
write

```
q = 1+beta*J,   k = eta+zeta,   L = q²-1,   N = q³,
X = q*w,       Y = N*s,        E = X*Y,
a = E+Y,       c = eta+k*Y,    P = k+E*(c-eta),
Delta = a²+4a+3,               D = X+a*c+(4a+3)*gamma,
V = f*o-c,     I = i*c²,       g = y²-V²,
R = ((q-1)*(q-F)+alpha)*L+(MC+MF_source*q)*J.
```

The seven residuals are exactly

```
tau²-(1+P*(P-k)),
D²-(1+c²*Delta),
k-(1+R+E*h),
c*j-V-R,
(K+w)*(q-F-alpha)-(F+(q-1)*z),
I²-Delta*(f²-1),
y²-I²*g-1.
```

`P*(P-k) = (X*Y²)*(X*Y²+1)*k²`. The strong norm is the ordinary
`I²=Delta*(f²-1)`, with `I=i*c²`. These coordinates are not silently
identified with those of the normalized strong equation.

The implementation reconstructs the original auxiliary coordinates in the
order `N,E,P,c,a,X,D,c²,L,f²,V,g,I,I²,Delta`. Every original source zero equals
this explicit lift of its first sixteen coordinates. Conversely, the lifted
source rows vanish exactly when the seven residuals do. The positive-domain
existence statement retains the positivity of all explicitly reconstructed
coordinates: in particular, it does not assume that `V>0` or `g>0` follows
without a separate argument. No computation or consistency interpretation is
attached to arbitrary coefficient ports.

The existing formal endpoints do not close authentic native calibration:

- [Jones1980.relaxed_aux](../HilbertTenthProblem/Lean/Diophantine/Paper1980/PellRelaxedMain.lean)
  exactly handles the ordinary strong equation once `c=psi_A(p)` and
  `c>A*(A²-1)²` have been established.
- [Jones1980.half_index](../HilbertTenthProblem/Lean/Diophantine/Paper1980/PellHalf90.lean)
  uses the plus-sign quotient conditions `u=J+j*c=c+o*f`. The selected source
  has `V=j*c-R=o*f-c`. The signed step-down argument is now checked in
  [NativePellStepDown.lean](Lean/DiophantineConsistency/NativePellStepDown.lean),
  with the recovered main sequence, large-size bootstrap and half-modulus
  bounds explicit. It accepts either sign of `V`, recovers the index
  without an oddness premise, and safely restores the strong quotient.
  The actual source must still supply those bootstrap hypotheses; the
  plus-sign theorem is not directly an instance. See
  [NATIVE_PELL_STEP_DOWN.md](NATIVE_PELL_STEP_DOWN.md).
- [KEndpoint215.blank_halts_iff_zfc_refutation](../BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean)
  already identifies the literal machine215 blank halting predicate with
  `BProv ZFCax_s [] Form.fBot`.

For the authoritative old-z source now bound by `SplitCertificate59`,
[NativePellBootstrap](NATIVE_PELL_BOOTSTRAP.md) has also closed main
classification, the native window bound, the strong bootstrap and the exact
main index from explicit native port relations. Its inner native rank is
distinct from the outer binomial rank. These are literal source arithmetic
theorems, not fixed-payload/tableau calibration; the package-52 shifted
quotient still needs its precise domain translation when reusing them.

The remaining external contract is the positive-zero
existence equivalence between this *particular coherent four-port instance*
and `BlankHalts machine215`. A useful decomposition is the seven-equation
Pell/bit-mask theorem, the literal complement-packed clause decoder, whole-cell
synchronization, and extraction/construction of a finite blank K215 tableau.
The inherited
[ordinary proof](con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_ORDINARY_PROOF.md)
and
[complement-packed coefficient proof](con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md)
explicitly describe ordinary mathematics rather than an end-to-end Lean/Rocq
certificate. Numeric bit-length or SHA checks do not discharge that contract.
The closed `NativeZFC` expression uses a different proof-enumerator graph and
Jones compiler, so its theorem does not identify these fixed native ports.

This missing external contract is also distinct from an object-language ZFC
proof of the final consistency/unsolvability biconditional; see
[OBJECT_ZFC.md](OBJECT_ZFC.md).
