# Independent review: the composed small-backend B4 equation

## Verdict and exact scope

**PASS.** The new nonzero-word coefficient backend can be composed with the
literal 31-positive-variable parent and the B4 ten-integer reduction. The
review found no additional positivity, transport-coordinate, coefficient-bound,
or polynomial-degree obstruction.

This review supplements `B4_INDEPENDENT_REVIEW.md` and the independent backend
review in `../coefficient_backend/INDEPENDENT_REVIEW.md`. It addresses the
composition that was deliberately absent from the first B4 package. The old
`../ten_integer/` instance is retained separately. The present fixed instance
is `../ten_integer_composed/data/INSTANCE.json`.

The conclusion is an ordinary mathematical proof review, with exact finite
certificates for the stated algebraic and numerical claims. It does not
replace the inherited unbounded native-compiler/Pell theorems, Sun's Lucas
theorems, or the K215/refutation endpoint by a proof-assistant certificate.

## 1. The exact parent and coordinate conventions

The 31-variable parent has SHA-256

    1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287.

Its bytes are unchanged. It has 22 quadratic residuals and the four symbolic
ports `beta,K0,MC,MF`. The active binding is the complete new tuple

    beta=B-1, K0=DC+B*DR, MC=MC_native,
    MF=MF_native+B-1, B=2^683195.

The parent uses the **old** positive transport variable `z_old`, written `z`
inside its JSON. Its equation is

    (K0+w)C+(q-F)-z_old(q-1)=1.

The retained59 system instead uses `z_new` and

    (K0+w)C=F+z_new(q-1).

These are exactly related by `z_old=z_new+1`. No y-coordinate substitution is
part of this transfer. The subsequent normalization for B4 coding replaces
every positive parent coordinate by its own `n_i+1`, including its old z and
its unchanged y; that is the usual positive-to-nonnegative normalization.
The ten unknowns of the final compressed equation are a separate tuple.

The parent and retained59 also use the same **ordinary** strong multiplier:

    I=i*c^2, I^2=Delta*(f^2-1).

P67 uses a normalized multiplier. When passing through P67 rather than the
ordinary retained system, the required substitution is
`i_parent=Delta*i_P67`. Identifying these two multiplier conventions without
this substitution would be incorrect. The delivered composition does not do
so.

## 2. Direct algebraic correspondence with retained59

Let `k=eta+zeta`, `q=beta*J+1`, `C=q-F-alpha`, and `H=4a+3`.
Eliminating the definitional equations of the literal parent gives

    L=q^2-1, N=q^3, X=wq,
    Y=sq^3, E=XY, a=E+Y, c=kY+eta,
    P=EkY+k, Delta=a^2+4a+3,
    D=X+ac+gamma H, C2=c^2, F2=f^2,
    V=of-c, I=ic^2, Baux=I^2.

Set `R=jc-V`. Its packing equation agrees with retained59 because

    (q-F)(N-q)-CL
      = [q(q-F)-C](q^2-1)

when `N=q(L+1)` and `L=q^2-1`. Moreover

    P(P-k)=(EkY+k)EkY,
    y^2-Baux*(y^2-V^2)=Baux*(V^2-y^2)+y^2.

Thus the parent's nondefinitional equations become precisely the two main
norms, auxiliary norm, index congruence, transport equation, ordinary strong
equation, and retained quotient equality of the inherited retained system.
This uses ordinary polynomial identities, with all four ports symbolic.

For a positive parent zero the old transport equation already gives

    (K0+w)C=F+(z_old-1)(q-1)>0,

so `C>0` without first assuming `z_old>=2`. The inherited unshifted retained
Pell argument then supplies `X=wq=2^R`, `R>3q`, and `F<q`. Therefore

    (z_old-1)(q-1)=(K0+w)C-F>0,

since `w>q>F` and `C>=1`. Hence `z_old>=2`, and `z_new=z_old-1` is positive.
This proof order avoids using positivity of the shifted coordinate to justify
the unshifted theorem that establishes it.

Conversely a positive retained59 solution gives `z_old=z_new+1>0` and all
the displayed auxiliary definitions. Their strict positivity is checked next.

## 3. Strict positivity of every added parent coordinate

All the new coordinates except V and g are immediately positive from their
definitions and the positive retained inputs:

| Parent coordinate | Positive expression |
|---|---|
| N | q^3 |
| E | XY |
| P | EkY+k |
| c | kY+eta |
| a | E+Y |
| X | wq |
| D | X+ac+gamma(4a+3) |
| C2 | c^2 |
| L | q^2-1, with q>1 |
| F2 | f^2 |
| I | ic^2 |
| Baux | I^2 |
| Delta | (a+1)(a+3) |

Here is a tuplewise argument for the two remaining coordinates; canonical
completeness alone is not being asked to cover an unexplained sign change.
Put `A=a+2`, so `Delta=A^2-1`. Before auxiliary-rank recovery, the inherited
first/main norm bootstrap gives

    c>A*Delta^2.

This is the bound in Section 4 of the pinned ordinary proof: it uses the
outer rank bounds, the first norm, the positive strict ratio `kY<c<k(Y+1)`,
and the main norm. It does not assume that the auxiliary expression V is
positive. Since `A>=3` and `Delta>=8`, the displayed bound implies
`c^2>4Delta`.

The ordinary strong equation now gives

    f^2=1+i^2*c^4/Delta > c^4/Delta > 4c^2.

As f and o are positive integers,

    V=of-c >= f-c > c > 1.

The retained auxiliary norm is

    I^2 V^2-(I^2-1)y^2=1.

Since `I=ic^2>1`, rearranging gives

    g=y^2-V^2=(V^2-1)/(I^2-1)>0.

The left expression shows that g is an integer. It is therefore a strictly
positive integer, as required by the literal parent. This proves that every
positive retained59 solution restores positive V and g. In the other
direction these are already parent coordinates. The restored coordinates
are uniquely determined, so the stated reductions introduce no extra
existence hypothesis.

As an alternative completeness-only check, the canonical Pell witnesses
satisfy `I V=chi_I(R)` and `y=psi_I(R)` with the inherited positive large
rank R. They give the same positive g. The tuplewise argument above makes
that additional specialization unnecessary for the parent transfer.

## 4. Why the new backend supplies the required Pell interface

The independently reviewed backend proves more than its four low mask
congruences. The following are the inherited arithmetic interface and the
corresponding new-backend facts.

| Requirement | New-backend fact |
|---|---|
| Fixed dyadic outer base | B=2^d, d=683195>=4 |
| Coherent transport/masks | All four ports copied from one authenticated tuple; MF is the shifted source port |
| Native mask bounds | 0<MC,MF_native<B-1 |
| Low congruences | MC=2 mod4 and MF_native=4 mod8 |
| Balanced population | pc(MC)+pc(MF_native)=d |
| Uniform carry control | rho=2^107 exceeds the exact conservative native carry threshold |
| Native decoding | Selector-first clause extraction, two synchronization anchors, unique whole-cell alignment, and nonzero-word occupancy propagation |
| Canonical strict slack | The inherited uniform estimate preserves 2C+F<q/3 through all allowed dummy changes |
| Actual rank control | The explicit controller tunes the actual packed R to d*w_spatial mod dN |
| Unbounded completeness | Arbitrarily large independent spatial/temporal padding by powers of the prime 135257 |

The first six facts supply the same numerical outer estimates used by the
ordinary retained proof, including `q>=16`, `R>3q`, `R<q^4-2`, and
`E>=q^4>R+2`. The latter facts provide the semantic compiler soundness and
the genuine canonical completeness witnesses, including positive alpha and
transport variables. The parent adds no new condition on the factorization
of d or on the prime used for canonical padding.

In particular, the old powers-of-five presentation is not a hidden parent
restriction. The new backend replaces that particular completeness
controller by its proved arbitrary-odd-factor controller. Soundness permits
all solutions and all relevant periods; it does not impose the canonical
prime-power shape on candidate solutions.

The backend also preserves the odd-rank and signed-domain promises recorded
in its proof. The present parent only needs its positive ordinary interface.
The B4/Sun integer compressor subsequently proves its own unrestricted
integer-domain equivalence to this fixed nonnegative source polynomial.

## 5. Independent literal binding and coefficient-bound audit

`audit_composed_binding.py` imports no builder or verifier. It performed
these exact checks on the delivered files:

1. Read and authenticated the unchanged parent bytes and its 22 residuals.
2. Expanded each residual after the 31 substitutions `x_i=n_i+1`, squared
   them, and summed them using independent sparse integer-polynomial code.
3. Reconstructed all 402 factorial-weighted coefficient recipes and compared
   every recipe exactly with `data/constants.json`.
4. Checked the coefficient of tau^4 is 1 and that the fifth residual has
   constant coefficient 1 after normalization. Thus the source has exact
   degree four and is positive at zero for every fixed port choice.
5. Decompressed each actual new port, authenticated its independent backend
   hash, and compared its bytes with the sibling backend's materialized port.
6. Recomputed a triangle-inequality bound for every weighted coefficient
   from the actual port bit lengths, checking all 402 individual bounds and
   the common exponent 2743487.
7. Checked the actual source-base payload is exactly `2^2743514`, with an
   even exponent and the required strict margin.

The active port bit lengths are

    (683195, 688546, 683195, 683196).

For every weighted coefficient c_alpha, the independently checked bound is

    |c_alpha|+1 < 2^2743487.

The factorial multiplier is a positive integer, so the same common bound
also bounds the unweighted source coefficients. Since

    48*33^4=56924208 < 2^27,
    beta_S=2^(2743487+27)=2^2743514,

the source coefficient margin used by the B4 proof still holds. This is a
recomputed bound for the new tuple, not a stale index or constant copied
from the old tuple. There are no new quantified parameters.

The exact payload identities and the symbolic coefficient hash are recorded
in `COMPOSED_BINDING_INDEPENDENT_AUDIT.json`. The new source-base SHA-256 is

    9b08a393d10913d6210c8849be93f0aa17f3b4b22d706715dbbc588f379654a3.

## 6. Independent final-circuit audit

The existing no-builder auditor was run with the composed directory as an
explicit argument and a separate output receipt. The literal arithmetic DAG
is unchanged; its fixed leaves acquire the new values through the active
instance. This means that the DAG hash alone does not identify the fixed
polynomial. The binding manifest and coefficient payload hashes are essential
parts of its definition.

All checks passed:

| Property | Independently verified result |
|---|---:|
| Unrestricted integer unknowns | 10 |
| Binary additions | 485 |
| Binary subtractions | 25 |
| Binary multiplications | 1694 |
| Total arithmetic operations | 2204 |
| Total degree upper bound | 107286763576 |
| Distinct padded B4 four-sums | 52360 |
| Independent named formula comparisons | 882 |
| Dead nodes or nonpolynomial gates | None |

The degree is exact. On substituting every unknown by one indeterminate,
the coefficient at the reported upper degree is nonzero with the actual new
fixed coefficients:

| Prime | Leading coefficient modulo that prime |
|---:|---:|
| 101 | 36 |
| 1009 | 63 |
| 1000003 | 258712 |

One nonzero row already proves attainment of the upper degree. The modular
formula comparisons are transcription diagnostics; they are not substitutes
for the mathematical B4 and bridge proof. The B4 uniqueness and diagonal
leading-coefficient computations are exact finite certificates for those
specific claims.

## 7. Reproduction and dependencies

From the package root run:

```sh
python review/audit_composed_binding.py
python review/audit_b4_independent.py ten_integer_composed review/COMPOSED_B4_INDEPENDENT_AUDIT.json
```

The first command writes `COMPOSED_BINDING_INDEPENDENT_AUDIT.json`. Both
auditors use only the Python standard library and do not import the builders.
The original B4 audit receipt is not overwritten by these commands.

The mathematical transfer uses the exact pinned quartic31 source proof
copied into `../ten_integer_composed/source_proofs/QUARTIC31_PROOF.md`, the
ordinary retained/Pell argument, and the independently reviewed new backend.
The primary repository snapshot is
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`:

- [Literal quartic31 source proof](https://github.com/VladimirReshetnikov/ProveIt/blob/22e75dd6b87b1b199bb08c778d7cf075ae5aae08/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/31-sun10/sources/QUARTIC31_SOURCE_PROOF.md).
- [Ordinary Pell/compiler proof](https://github.com/VladimirReshetnikov/ProveIt/blob/22e75dd6b87b1b199bb08c778d7cf075ae5aae08/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/31-sun10/sources/ORDINARY_BLANK_PROOF.md), especially Sections 3, 4, and 7.
- [Inherited retained59 proof](https://github.com/VladimirReshetnikov/ProveIt/blob/22e75dd6b87b1b199bb08c778d7cf075ae5aae08/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_RETAINED59_PROOF.md).
- [Sun 2021](https://arxiv.org/html/1704.03504v7) and [Sun 2026](https://arxiv.org/html/2609.01594v2), as specified in the B4 and inherited bridge reviews.

With these stated dependencies, the fully fixed composed polynomial has an
integer zero exactly when the new backend's marked blank K215 computation
exists, hence exactly when the chosen ZFC proof predicate has a finite
refutation. ZFC proves the corresponding equivalence of no integer zero
with Con(ZFC). This is the composed conclusion, not a decision of Con(ZFC)
or a claim of global minimality.
