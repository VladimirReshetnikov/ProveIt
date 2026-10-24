# Ten positive integers, 105 operations, exact degree 340

The complete equation is `N=0` in equation.json, with the ten strictly
positive inputs `J,F,alpha,i,T,x,Y,n,eta,zeta` and the four fixed
coherent compact44 coefficients. It has **105 live operations**:
63 multiplications, 24 additions and 18 subtractions. Its exact total
degree is **340**; syntactic propagation before cancellation gives384.
This improves the accepted direct-base107/340 circuit by two operations.
It offers a degree tradeoff with the accepted zero-offset99/368 equation.

The new full Pell base is

    X=q+x, a=Y(X+1), A=mu*a+1, mu=q²+1.

The existing product `muY=mu*Y` is shared in
`Am1=muY*(X+1)`. The universal identity
`mu*(X*Y+Y)=(mu*Y)*(X+1)` makes the stored graph exactly equal to
the unshared106-operation direct zero-offset polynomial. The old
direct107 parent instead has `A=mu*(a+2)+1`; its polynomial is different.

CUTS.json accounts for every one of the107 direct-parent definitions.
It deletes only the private E,a,a2 definitions, inserts Xp1=X+1,
moves the existing muY before Am1, and replaces Am1's multiplication.
All other literal rows, including the full13-operation weighted norm,
are retained. Literal `a` is absent from the graph and remains a proof
abbreviation. ZERO_PARENT_CUTS.json separately accounts for all99
zero-offset-parent definitions and all six inserted direct-carrier rows.
The two complete circuit constructions give the same stored105 rows.

The ordinary proof uses only `X>q>=32` through the first index,
ratio and whole-product projection arguments. The enlarged carrier is
`P=q⁴(q-1)`, and the center includes `-X/q⁴`. It proves `X=2^R`
before deriving `q|X`; it never cancels H modulo q prematurely.
The same argument then gives `q⁴|X` and the source transport quotient.
The reconstructed unscaled source retains its prescribed base `a+2`.

Completeness starts from an accepted99/368 zero-offset zero. It keeps
X and all kernels, sets `x=X-q>0`, and uses

    n_new=n99+(W_new-W99)*t+X/q⁴,
    t=Bt/(q-1)>=0, W_new-W99=(q-1)²L>0.

The complete numerator identity in PROOF.md gives `Z_new=q*Z99` and
`M_new=q*M99`, hence the whole norm output is `q^8` times the old
output. Positivity holds also at `t=0`. A positive pointwise inverse
map is not asserted. The focused ordinary peer is copied and pinned
under source/COMBINED_ORDINARY_PEER.*.

The independent checker imports neither producer nor historical
emitter. It checks both complete row maps, topology, liveness, whole
parent manifests, copied ordinary/source dependencies and all four
compressed and raw coefficient payloads. It checks recursive literal
front and carrier cuts, all35 independent weighted norm coefficients,
the signed-root identity, centered cancellation, ratio-cut identities
and the full licensed numerator and norm-scaling identities.

After `Z=M*V+Z0`, the bounds are `deg Z0<=24` and omega-term degrees
`74,85,70,26`. The complete centered norm has a unique top `omega^4`.
With `q0=beta*J` and `X0=q0+x`, its degree85 omega leading form is

    2^7*q0^39*X0^9*i^5*Y^19*(eta+zeta)^10*B0*(q0-F),
    B0=(q0*K0+X0)*(q0-F-alpha)-q0*F.

The checker compares all1155 terms of this form. The highest-x part
has55 terms; its fourth power has1435 terms and gives the nonzero
coefficient `2^28*beta^156` at
`J^156*x^40*i^20*Y^76*eta^40*alpha^4*F^4`, of total degree340.
Actual-tuple degree lines, exact signed-integer and rational controls,
and licensed-center controls supplement the universal identities.
Seven targeted circuit/domain/coefficient mutations are rejected.

The complete original compact44 tuple is unchanged, including its
already shifted MF. Both parent proof/source collections are copied
and pinned. The separate coherent BFS tuple remains licensed by the
inherited uniform native/controller source proof; different K0 values
are never identified, and individual ports are never mixed.

The unbounded positive-zero/refutation equivalence is the ordinary
proof in PROOF.md, with the explicitly pinned source61/native
calibration. This packet adds no Lean or internal-ZFC theorem. All
accepted parents, historical emitters and canonical page are unchanged.

```sh
python -B Computability/DiophantineConsistency/tools/build_ten_positive_direct_zero_offset.py --check
python -B Computability/DiophantineConsistency/candidates/ten-positive-direct-zero-offset/check.py
python -B -O Computability/DiophantineConsistency/tools/build_ten_positive_direct_zero_offset.py --check
python -B -O Computability/DiophantineConsistency/candidates/ten-positive-direct-zero-offset/check.py
```

The four replay logs and both checker receipts are included. MANIFEST.json
lists every packet member and its SHA256; no external build records are
needed to reproduce this packet's checks.
