# Composing additive coding with the nonzero683195 compiler

## Result

The fixed equation in generated/b4_signed10.json has ten unrestricted
integer unknowns, exact total degree 107286763576, and 2204 binary
arithmetic operations. It combines the B4 source coding proved in
../ten_integer/PROOF.md with the complete smaller coefficient tuple proved
in ../coefficient_backend/PROOF.md. It is a different fixed polynomial
from the comparison instance in ../ten_integer/, although its arithmetic
DAG and variable list are identical.

ZFC proves that this equation has an integer zero if and only if there is
a finite ZFC refutation for the pinned repository's proof predicate.
Negating gives the requested equivalence with Con(ZFC). The inherited
K215, native compiler, Pell and Sun theorems are the same mathematical
dependencies as in the comparison instance. The finite checks are not a
new end-to-end formal certificate or a consistency proof.

## 1. The exact parent transfer

The literal parent is unchanged:
data/parent_quartic31.json has SHA-256

    1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287.

Its 31 positive variables, 22 quadratic residuals and positive-to-natural
shift are the same as in the comparison construction. Historical tuple
metadata inside that byte-preserved source is inert. The new active
instance is specified in data/INSTANCE.json and
data/coefficients_binding.json.

Use the sixteen strictly positive retained59 variables

    J,F,alpha,z_new,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma,

and the complete new four-port tuple. Put

    q=beta J+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H, D=X+ac+gamma H,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    V=of-c, I=ic^2, A0=Delta(f^2-1), L0=E kY.

Name the seven retained residuals

    u1=tau^2-L0(L0+k)-1,
    u2=D^2-Delta c^2-1,
    u3=A0(V^2-y^2)+y^2-1,
    u4=k-hE-R-1,
    u5=(K0+w)C-F-z_new(q-1),
    u6=I^2-A0,
    u7=jc-R-V.

They are exactly the equations bound to the new tuple in
../coefficient_backend/equations/retained16_system59_nonzero683195.json.

Extend a retained solution by

    z_old=z_new+1, N=q^3, L=q^2-1,
    P=E(c-eta)+k, C2=c^2, F2=f^2,
    Baux=I^2, g=y^2-V^2,

together with the displayed expressions for E,c,a,X,D,V,I,Delta.
The parent uses z_old. Its y is unchanged. The outer ten-integer
variables named y and z belong to a later reduction and are distinct
from these parent variables.

All fifteen added coordinates are automatically positive except that V
and g deserve a proof. The inherited first/main-Pell bootstrap for the
ordinary retained kernel (source_proofs/ORDINARY_BLANK_PROOF.md,
Section 4, equation (3)) gives c>A Delta^2, where A=a+2 and
Delta=A^2-1. This estimate precedes auxiliary rank recovery; it follows
from the first-norm index n>=24, the main index p>n, and elementary Pell
growth. In particular c>2 and c^2>4 Delta. The ordinary strong equation
u6=0 gives

    f^2=1+i^2 c^4/Delta > 4c^2.

Thus f>2c. Since o is a positive integer, V=of-c>c>1. Combining u3=u6=0
gives

    I^2 V^2-(I^2-1)y^2=1,
    g=y^2-V^2=(V^2-1)/(I^2-1)>0.

The last ratio is an identity between integers; I=ic^2>1. This proves
positivity for every positive retained59 solution, not merely for a
specially chosen canonical solution.

The ordinary multiplier i here must not be confused with the normalized
multiplier in P67. P67's canonical normalized coordinate is
i_P=psi_A(m)/c^2. The retained parent uses
i=Delta*i_P, so I=Delta*psi_A(m). The two forms have different strong
equations. This composition binds the ordinary retained system directly
and does not identify these coordinates.

Now substitute the extensions into the 22 literal parent residuals.
All vanish identically except the seven in positions 8,12,13,14,15,21,22,
which respectively become

    u1, u2, u4-u7, u7, u5, u6,
    u3+(V^2-y^2)u6.

The packing identity used here is

    (q-F)(N-q)-C(q^2-1)
      = [(q-1)(q-F)+alpha](q^2-1)

when N=q^3. The transport identity is

    (K0+w)C+q-F-z_old(q-1)-1
      = (K0+w)C-F-z_new(q-1).

Thus every positive retained59 solution extends to a positive parent
solution with exactly the stated coordinates.

Conversely, a positive parent solution has q>1, and its transport
equation gives

    (K0+w)C=F+(z_old-1)(q-1)>0.

Hence C>0 and F<q. Restore the deleted packing coordinate

    G=q(q-F)-C=(q-1)C+q alpha>0.

The literal packing identity in source_proofs/QUARTIC31_PROOF.md restores
the complete positive quartic32 source. Its authenticated ordinary kernel
gives X=wq=2^R and R>3q. Therefore w>q>F. It follows that

    (z_old-1)(q-1)=(K0+w)C-F>0,

so z_new=z_old-1 is strictly positive. The same identities recover all
seven retained equations. The two maps are inverse once the added
coordinates are restored by their defining equations. This proves the
tuplewise positive zero-set equivalence, including all sign obligations.

The new backend's full compiler-adapter theorem proves the retained59
existence/refutation equivalence for precisely this coherent tuple.
Therefore it proves the same equivalence for the literal positive
31-coordinate parent. Replacing every positive coordinate by n_i+1
gives the required quartic P0 over N^31. No source witness or dummy input
is added. P0(0)>0 still follows from the fifth residual
E-X(a-E)=1 at the all-one assignment.

## 2. New fixed coefficients and source margin

All four native ports are copied together, byte for byte, from the new
backend. Their bit lengths, in order beta,K0,MC,MF, are

    683195, 688546, 683195, 683196.

MF is the already-shifted source mask, not the native high mask.
The native base is 2^683195. The four uncompressed payloads total
342269 bytes.

The symbolic weighted-coefficient recipes are unchanged. For each of the
402 records write

    c_alpha = sum_e a_(alpha,e) A_1^e1 ... A_4^e4,

where the four positive ports A_j have bit lengths b_j. Set

    U_alpha = sum_e |a_(alpha,e)| 2^(sum_j e_j b_j).

Then |c_alpha|<=U_alpha. The regenerated certificate individually checks
all 402 values and their strict power-of-two bounds. Their maximum is

    |c_alpha|+1 < 2^2743487.

Since c_alpha is a positive factorial multiple of p_alpha, this bounds
H=max|p_alpha| as well. Choose the new actual fixed integer

    beta_S=2^2743514.

Its exponent is even, and

    2*24*33^4=56924208 < 2^27,

so beta_S>2*24*33^4 H, precisely the bound required by the B4 source proof.
The integer beta_S is materialized in data/beta_sun.bin.gz, with an
unsigned little-endian decompressed length of 342940 bytes and SHA-256

    9b08a393d10913d6210c8849be93f0aa17f3b4b22d706715dbbc588f379654a3.

The four native ports and beta_S total 685209 uncompressed bytes, compared
with 1066835 for the comparison ten-integer instance: a 35.77% reduction.
This compares five fixed payloads within the ten-integer construction;
the separate backend's comparison against package36 concerns four ports.

## 3. The same B4 interface and outer equation

Use the identical code weights, T=942302, Lc=4T, coefficient convention,
source formulas, Lucas bridge and final norm from ../ten_integer/PROOF.md,
replacing all four native coefficients and beta_S by the values just
specified. Every hypothesis of that proof has been checked above:
31 natural variables, degree four, P0(0)>0, fixed integer coefficients,
the four-sum code, and the strict beta_S margin. The source soundness and
arbitrarily large completeness witnesses therefore apply unchanged.

The arithmetic graph is exactly the comparison graph: 485 additions,
25 subtractions and 1694 multiplications, with ten variable leaves and
79 fixed coefficient leaves. Fixed values differ but no new variable or
arithmetic operation is introduced. The degree upper bound remains

    113856*942302+27064 = 107286763576.

The new actual coefficients give nonzero diagonal leading coefficients
36 mod101, 63 mod1009, and 258712 mod1000003. Any one proves that the
degree upper bound is attained. The proof of ZFC equivalence now composes
the authenticated parent transfer with the B4 source lemma and the same
Sun2026/package31 outer bridge.

## 4. Reproduction and evidence boundary

Run, with only Python's standard library:

    python3 regenerate_binding.py
    python3 b4_code.py
    python3 build_b4_sun10.py
    python3 verify_b4_sun10.py

Paths resolve relative to the scripts, not the caller's working directory.
The first script reads sibling coefficient_backend and ten_integer data,
recomputes every coefficient bound and the even beta_S exponent, copies
the complete tuple, and regenerates all active binding metadata.
The remaining three commands regenerate and audit the main equation.
Only the main structural-quintic variant is emitted in this folder.

The independent scripts and receipts in ../review/ do not import this
builder or verifier. They separately reconstruct the 402 coefficients,
check the full byte binding and bounds, audit the circuit and source
formulas, and certify the new exact degree. No finite diagnostic is
claimed to establish the inherited universal halting/compiler/Pell/Sun
results.

Attribution and exact source identities are recorded in SOURCE_PINS.json,
NOTICE.md, source_proofs/ and licenses/. The base code retains its package31
attribution; the nonzero backend is identified by its sibling binding and
proof. This folder defines a new active specialization rather than
rewriting or relabeling the comparison equation.
