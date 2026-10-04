# Two bounded producer checks on the actual complete84 source

No operation reduction results. The main/input root reassociation remains
**84 = 47M + 37A**. Reusing the first-root product to build the main center
instead gives **87 = 48M + 39A**. These are all-value arithmetic rewrites,
with the same 18 positive witness coordinates, ordinary input, fixed numeral
ports, seven factors, finalizer and exact degree187 as the pinned parent.
No universality proof or coordinate inverse is newly required.

This is a fresh bounded scout, not a maintained compiler API or an
arithmetic lower bound for the actual whole polynomial. The helper reads the
parent files as inert bytes/JSON and imports no predecessor software.

## Source and coverage

The parent directory is supplied by `--root`. Its authenticated files are:

| File | SHA256 |
|---|---|
| complete84_scaled_strong_output.py | 8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737 |
| complete84_scaled_strong_output.json | 8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf |
| complete84_scaled_strong_output.md | 01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade |

The parent proof and complete source were read. The existing
`complete87_joint_norm_scout`, `complete87_shared_coefficient_scout`,
`complete87_discriminant_shear_scout` and
`complete84_local_producer_scout` notes were read to delimit already covered
norm compositions, common coefficients, affine discriminant shears and local
single-output rewrites. None of those helpers was run.

Frozen helper SHA256:
`d110b0ef43e223af1748eabe80dbd3e53c3acb2a59c766e7e581e74dbd87ae87`.
New receipt SHA256:
`c8f8e2175f49f1b41aab0c91658da5e4dd8da1f9b7f2584abdf72fbba43e307f`.
The [helper](complete84_joint_root_cut.py) and [receipt](complete84_joint_root_cut.json) save the full unchanged parent packet and both complete alternate
source arrays, including every finalizer row.

## Joint main/input roots

At the source ports

```
a=R12, H=a4m5, c=R10a, kappa=index_rhs, X=wn2,
D=R14, mu=exponent_rhs,
```

the two roots are

```
D  = a*c + X + (rho+sigma)*H,
mu = a*kappa + W + rho*H.
```

The actual nine-row source uses 4M+5A: two center multiplications, two
multiplications by H, the gamma addition, and four root additions. Sharing
`rho*H` across the roots changes their construction to

```
ac=a*c; base=X+ac;
rhoH=rho*H; sigmaH=sigma*H;
D=(base+rhoH)+sigmaH;
ak=a*kappa; mu=(W+ak)+rhoH.
```

This also costs 4M+5A. The helper proves both root identities by exact sparse
coefficient expansion at the eight independent ports. It replaces all nine
old rows, preserves the retained `modulus_multiple=rhoH` register, orders the
whole source by dependencies and rejects any dead or missing row. Exact
expression interning after the two proved cuts checks all seven factors and
the final polynomial. The actual result has all84 rows live and costs47M37A.
Thus every consumer is retained and the full polynomial identity holds over
any commutative ring, including every signed, rational and positive tuple.

There is a useful restricted lower bound for this cut. Treat a and H as
independent left inputs and c,kappa,rho,sigma as independent right inputs.
Allow separated homogeneous bilinear products of linear forms in these two
sets, paid linear preprocessing/postprocessing, and attach X and W by two
separate final additions. This excludes nonlinear intermediate products and
cancellation between higher-degree terms. The coefficient flattening of the
two offset-free outputs, with rows `(a*out1,a*out2,H*out1,H*out2)`, is

```
             c  kappa rho sigma
             1    0    0    0
             0    1    0    0
             0    0    1    1
             0    0    1    0
```

It has rank4. Each separated bilinear multiplication contributes rank at
most1, so at least four are needed. A core with at most six total gates would
therefore have at most two additions. Combining at least four live bilinear
products into two outputs already requires at least two postprocessing
additions. There is then no addition available for preprocessing. Each
product is consequently a scalar multiple of a single raw monomial. The
three-monomial first output needs both additions; its only two-term
intermediate cannot be the second output, which contains `a*kappa` absent
from the first. Hence at least three core additions are needed. The core
cost is at least7, and the two explicit offset attachments make9, attained
by both schedules above. Scalar multiplications cannot reduce this gate
bound. A supplementary exhaustive 3,600-case enumeration of two raw
addition/subtraction gates agrees; that finite enumeration alone is not the
proof for arbitrary scalar coefficients.

The restriction is substantial: the actual source has **H=4a+3**, and the
other cut ports also have producers. This lower bound does not exclude
exploiting those relations, sharing with norm factors or other producers,
allowing nonlinear cancellation, or using a sound new positive-coordinate
map. It does not establish a nine-gate minimum for every actual-root circuit.

## First/main overlap

Let `E=UM`, `Y=sn2`, `kY=ksn2`, and `U=first_root_base=E*kY`.
The actual definitions are `a=E+Y` and `c=kY+eta`, so

```
a*c = U + E*eta + Y*c.
```

This exact reuse of the paid first-root product replaces one multiplication
by two multiplications and two additions. The original U remains needed in
the first norm, and E, Y and c retain their other consumers. The helper
checks those defining rows literally, verifies the coefficient identity,
emits the whole alternate source and checks all87 gates live. Its cost is
48M39A: a loss of1M2A. This rules out this specific expansion as a saving;
it is not an exhaustive lower bound for all first/main recombinations.

## Fresh checks and limits

Fresh normal and optimized Python runs from `/` produce byte-identical
receipts. In addition to the formal coefficient and downstream-DAG checks,
the root-sharing source passes64 complete assignments, including32 rational
assignments; the first/main expansion passes16, including8 rational ones.
All seven factor values and the final output are compared. These are
supplementary arithmetic checks, not constructed full positive zeros.

```
scout_wip=/absolute/path/native-stream-queue
python3 "$scout_wip/complete84_joint_root_cut.py" --root "$scout_wip" \
  --output /tmp/complete84_joint_root_cut_fresh.json
python3 -O "$scout_wip/complete84_joint_root_cut.py" --root "$scout_wip" \
  --output /tmp/complete84_joint_root_cut_optimized.json
cmp "$scout_wip/complete84_joint_root_cut.json" /tmp/complete84_joint_root_cut_fresh.json
cmp /tmp/complete84_joint_root_cut_fresh.json /tmp/complete84_joint_root_cut_optimized.json
```

The concrete remaining opening is a larger cut that uses H=4a+3 or changes
how the factors are evaluated jointly. The existing finite discriminant-shear
study already covers the obvious completed-square forms, so reproducing that
census would add no new evidence. No improved universal operation bound is
claimed here.
