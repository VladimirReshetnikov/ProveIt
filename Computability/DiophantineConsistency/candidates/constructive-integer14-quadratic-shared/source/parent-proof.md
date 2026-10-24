# Fourteen unrestricted integers, degree312,121 operations

This new signed endpoint has **14 unrestricted integer unknowns**, exact
total degree **312**, and **121 live binary operations**:70
multiplications,26 additions and25 subtractions. It retains the complete
six-port source34 tuple of the frozen degree568/145-operation parent.
The complete literal equation is the final output of `equation.json`
set equal to0. Every leaf, gate, unknown and fixed port is live.

The full new ordinary proof is [PROOF.md](PROOF.md). It is an equivalence
of **integer-zero existence** with the parent, with explicit unrestricted
n maps. It is neither a pointwise identity of the two polynomials nor a
silent application of a positive-domain result to signed coordinates.
The parent and its native calibration are used only after a complete
old integer zero has been restored.

The unchanged guard first licenses v!=0, c!=0 and delta>0 at a zero.
Three-root separation yields integral f,tau,y at the weak scale Y=qv.
Absolute-value Pell classification and all-index psi folding then recover
`|c|=psi_|a+2|(p)` for some p>=1. This handles both signs of A=a+2,
c, I and V before the cubic scale or any orientation is known.

Replace the old b0=X+ac in its coprime CRT center by

```
K=X*(X+2*a*c)-1,
M=2*q^2, U=M*H,
Z=U*(n+V)+M*K+H*(v-q^2).
```

The center first recovers `Y=(2*v_old+1)*q^3` and H|K. The precisely
identified signed-bootstrap prefix, copied as
`source/RESIDUE_AND_DETERMINANT.md`, now applies before its main-projection
step: it gives p=R odd and the sign-uniform lower bound on |Y|.
For sigma=sign(c) and x=|X|, a new absolute height argument gives

```
H | (sigma*X-2^R)*(2^R*sigma*X+1),
abs((sigma*X-2^R)*(2^R*sigma*X+1)) < abs(H).
```

Therefore sigma*X=2^R; the second factor is odd and cannot vanish even
when sigma*X is negative. This restores a signed integer main root d
with H|(d-b0). No positive sign or coprime-factor cancellation is assumed.
Changing only the unrestricted n then maps back to a complete old zero.
The reverse map is integral for every old zero and needs no positivity
of its new n.

The literal new norm is the denominator-cleared octic

```
fs=delta*Z^2,
fa=delta*U^2*Df, fb=delta*U^2*Dtau, fc=U^2*Cy,
N=((fs+fc-fa-fb)^2-4*(fs*fc+fa*fb))^2
    -64*(fs*fc)*(fa*fb).
```

It computes exactly delta^4 times the three-radical norm before
clearing. The finalizer remains `N+S+N*S`, S=guard^2, whose integer zeros
force both N and the guard to0 even when N is negative elsewhere.
No quantified coordinate is introduced by any abbreviation.

The norm has exact degree256. The guard raises the final degree to312,
with nonzero actual coefficient

```
[j^140 w^48 v^60 h^12 r^16 c^32 z^4] P
    =2^280*3^188*beta^140.
```

The complete leading-form argument is in the proof. Syntactic bounds
are288 for N and344 for the output; finite degree lines are supplemental,
not the unbounded upper-bound proof.

`check.py` imports no candidate builder or author verifier. It independently
checks the full35-term cleared norm, both projection identities, complete
prefix/deletion/replacement/finalizer coverage, all six actual coefficient
payloads, topology and liveness. It verifies100 complete signed-input
formula controls including v=0 and c=0, four actual-six-port degree lines
with both predicted leading coefficients, signed folding/classification,
negative-X projection and height controls, and deliberately corrupted
norm and projection operations. The mathematical peer review is retained
separately under `source/` with its exact proof hash and normal/-O results.

From the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/build_constructive_integer14_quadratic.py --check
python -B Computability/DiophantineConsistency/candidates/constructive-integer14-quadratic/check.py
python -B -O Computability/DiophantineConsistency/tools/build_constructive_integer14_quadratic.py --check
python -B -O Computability/DiophantineConsistency/candidates/constructive-integer14-quadratic/check.py
```

All pass. `VERIFICATION.json` records the commands, and `MANIFEST.json`
seals the packet. All earlier candidates, incoming archives, PDF/TeX and
common documents remain untouched. This improves this integer parent in
degree and operation count without changing its domain or coefficient
tuple; no global minimum is claimed. Lean remains paused, and the
outstanding internal-ZFC formalization/calibration boundary is unchanged.
