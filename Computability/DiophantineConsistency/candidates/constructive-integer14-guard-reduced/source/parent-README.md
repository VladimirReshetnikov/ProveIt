# Fourteen unrestricted integers, degree312,119 operations

This separate **119-operation evaluator** computes exactly the frozen
121-operation signed quadratic-projection polynomial. It retains all14
unrestricted integer unknowns, exact degree312, the degree256 norm, and
all six original coefficient payloads. Its68 multiplications,26 additions
and25 subtractions are all live. The complete equation is the output of
`equation.json` set equal to0.

The two universal prefix identities are

\[
q(2q)=2q^2,\qquad
\ell(\ell+1)k^2=(\ell k)(\ell k+k).
\]

The first reuses q^2, already computed for the native rank, instead of
computing2q and multiplying by q. The second computes L=ell*k and L+k,
then their product, replacing the three private intermediates ell+1,
ell*(ell+1), and k^2. Each cut saves one multiplication. Both identities
hold in every commutative ring, with no sign, nonzero or Pell premise.

Every remaining leaf/gate and every named register is remapped exactly.
The changed cut outputs have the same values by the displayed identities;
induction along the rest of the graph proves equality at every retained
register and at the entire final output. Consequently this is a pointwise
polynomial identity, including all exceptional assignments before the
guard is imposed. No new witness map or ordinary calibration claim is
needed.

`NODE_REMAP.json` accounts for all148 parent nodes and146 child nodes.
Four removed private intermediates have their old defining expressions
recorded for restoration, and the two newly inserted L/L+k gates are
identified. The removed values are not falsely equated to individual
retained nodes. All their original uses are confined to the two declared
cuts. Every named register and the final output retain their values.

The unbounded signed proof is copied as `source/ordinary-proof.md`,
SHA256

```
dfd78f5cf75133bdfd1a260be108fcac4663e71e97ca4a85dbf36f1a0d75da4c
```

It handles signed A,X,Y,c,V by absolute Pell folding, recovers the cubic
scale before the signed bootstrap, resolves the quadratic projection by
a whole-product absolute bound, and uses unrestricted n maps. Its
independent mathematical peer, full formula binding and normal/-O
receipts are retained. All this arithmetic and the inherited native
boundary transfer unchanged through the exact evaluator identity.

The degree proof transfers too, including the positive actual coefficient

```
[j^140 w^48 v^60 h^12 r^16 c^32 z^4] P
    =2^280*3^188*beta^140.
```

The syntactic bounds remain344 for the final polynomial and288 for the
norm. The actual degrees312 and256 do not rely on finite tests alone.

The independent checker verifies both local sparse-ring identities,
complete coverage and sole-use facts, all35 coefficients of the unchanged
cleared norm, every coefficient byte, topology and complete liveness.
It compares all retained node values on100 actual-port controls including
v=0/c=0, restores each removed private value, and checks50 signed
free-coefficient controls. Two complete actual-six-port lines attain
degrees312/256. Wrong cut signs, factors and operands are rejected.
No candidate builder or author verifier is imported.

From the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/build_constructive_integer14_quadratic_shared.py --check
python -B Computability/DiophantineConsistency/candidates/constructive-integer14-quadratic-shared/check.py
python -B -O Computability/DiophantineConsistency/tools/build_constructive_integer14_quadratic_shared.py --check
python -B -O Computability/DiophantineConsistency/candidates/constructive-integer14-quadratic-shared/check.py
```

All pass. Command receipts are in `VERIFICATION.json`; `MANIFEST.json`
seals every packet file. The121 parent, all earlier packets, PDF/TeX and
common documents remain untouched. Lean remains paused, and the
outstanding internal-ZFC formalization is unchanged. No global operation
minimum is claimed.
