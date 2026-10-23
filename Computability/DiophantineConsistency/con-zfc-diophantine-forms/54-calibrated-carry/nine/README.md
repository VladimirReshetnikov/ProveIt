# Nine-natural and nine-positive sparse calibrated equations

Each generated circuit defines one literal integer polynomial in exactly nine
unknowns. All named registers are abbreviations, not additional unknowns.
Binary addition, subtraction and multiplication are counted, including scalar
multiplications. Reuse and integer constant leaves are free. All powers have
fixed nonnegative exponents and are lowered to these binary gates.

## Domains and complete polynomial

The nine inputs are `b,g,h,s,w,phi,i,j,n`.

- Positive circuits: all nine inputs are strictly positive; internal phi,j,n
  are their input values minus one. Internal b,g,h,s,w,i equal the inputs.
- Natural circuits: all inputs are nonnegative; internal b,g,h,s,w,i are
  their input values plus one. Internal phi,j,n equal the inputs.

These are bijective domain translations. In particular the internal CRT
quotient j is allowed to be zero. The endpoint internal b=1 is harmless:
its mask would force the forbidden all-zero source tuple.

The complete source is defined and proved in
`../source/SPARSE_POPCOUNT_SOURCE_PROOF.md`. It produces polynomial R,N,b,g
and Gcap, satisfying the unconditional Jones ratio hypotheses. Source L and
threshold N are different polynomials. For odd Kcode the extra b factor in N
is essential.

The CRT-reparameterized arithmetic registers and final polynomial are the
literal nodes in each JSON and the definitions in `ratio_tail.py`. Write
scale=64 or 2048^2 according to the selected majorant, and put

Omega=J*m,
Theta=J*n+Q-Omega*(V0+V1),
F9=(Theta^2-Omega^2*(a0+scale*a1))^2
   -4*scale*Omega^4*a0*a1.

The equation is F9=0. `REFINED_MAJORANT_PROOF.md` gives the new quotient
majorant; `ratio_tail.py` also retains the simple64 and support2048 variants.
The inherited compiler/calibration and Jones ratio theorem remain explicit
mathematical dependencies. No global minimality, consistency proof, or new
end-to-end Lean/Rocq formalization is claimed.

## Artifacts and validation

- `generated/`: 28 retained primary, translated and degree-certificate circuits.
- `METRICS.json`: exact live binary-operation counts and degrees of retained
  positive/natural equations.
- `SEARCH_METRICS.json`: a finite comparison of 27 position/tail combinations;
  these are bounded candidates, not an optimality certificate.
- `FIXED_BINDING.json` and `fixed/*.bin.gz`: every live fixed leaf, materialized
  as a signed integer with hashed unsigned little-endian magnitude. Native
  coefficient payloads and their complete binding are in `../native`.
- `SOURCE_CIRCUIT_VERIFICATION.json`: exact equality of every Dcode and target
  polynomial in Z[B,beta,K0,MC,MF], including selective homogeneous source
  sharing and the geometric target sum.
- `REFINED_MAJORANT_CHECKS.json`: locally authored majorant diagnostics.
- Independent final composition and degree checks are supplied separately by
  the audit directory; finite tests do not replace the universal proofs.

The quotient2048 degree is 154r+328n+4c+196, where r=deg R, n=deg N and
c=deg Gcap. The support2048 formula is 158r+344n+4c+204; simple64 is
188r+400n+4c+232. Exact defects resolve the otherwise hidden leading-degree
cancellations. The enormous certificate-form circuits are proof aids and are
not included in the advertised operation count of the primary equation.

## Reproduction

From the package root, run:

    python source/verify_selective_source.py
    python source/check_sparse_popcount.py
    python nine/build_nine.py
    python nine/verify_source_circuits.py
    python nine/materialize_fixed.py

These commands use the Python standard library. The optional source generator
`source/build_selective_source.py` requires SymPy. The optional
`nine/scan_variants.py` recomputes the finite comparison ledger without
changing generated circuits. Builders overwrite their generated outputs;
verifiers write only their verification receipts. No upstream executable is
imported or run.
