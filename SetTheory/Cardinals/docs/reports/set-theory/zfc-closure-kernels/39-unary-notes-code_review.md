# Formula generator and independent review

Date: 16 October 2026.

## What the theory artifact implements

`code/theory_spec.py` generates exact equality-free formulas using four
primitive constructors: falsity, membership, implication, and universal
quantification. Negation, conjunction, disjunction, biconditional, and
existential quantification are explicit expansions into those primitives.

The general matrix interface has the free roles x=0, y=1, and p=2. Bound
variables are unrestricted. Wrapper helper binders are fresh for every
variable occurring in the matrix, including its bound variables. The
fixed repair's binders are also fresh for the matrix and wrapper. The
output includes ordinary EPSC1 instances and both fused variants,
LB(rho,p) -> (DP and Hull(rho,p)) and
LB(rho,p) -> (BU and Hull(rho,p)), universally closed over p.

The preferred fixed repair is exact Binary Union:

    forall A B exists C forall y,
      y in C iff (y in A or y in B).

The exact incoming-profile Pairing sentence DP and the one fixed
two-parameter disjoint gate Theta are retained for comparison. The generic
two-parameter wrapper is used only to encode this explicitly identified
fixed gate; it does not enlarge the general unary matrix interface.

Reproduce from the archive's top directory:

```sh
python3 code/theory_spec.py --output results/theory_spec.json
```

## Measured formula sizes

| Formula | Primitive tree nodes | Exact named DAG nodes |
|---|---:|---:|
| DP sentence | 71 | 31 |
| BU sentence | 27 | 17 |
| Fixed gate matrix Theta | 47 | 29 |
| Universally closed EPSC[Theta] sentence | 191 | 65 |

The BU sentence saves 44 tree nodes and 14 exact named DAG nodes against
DP in this specified representation. Its displayed three membership
occurrences become six occurrences in the primitive tree because the
biconditional expansion duplicates its arguments; the DAG has three
distinct membership nodes.

| Matrix | Ordinary EPSC1 tree/DAG | Fused DP tree/DAG | Fused BU tree/DAG |
|---|---:|---:|---:|
| False | 52 / 36 | 128 / 69 | 84 / 55 |
| y in p | 52 / 37 | 128 / 70 | 84 / 56 |
| Delta(y,p) | 85 / 44 | 161 / 77 | 117 / 63 |
| Bound-variable shadowing control | 64 / 41 | 140 / 74 | 96 / 60 |

The counts charge each formula constructor once per tree occurrence or
once per identical named subformula in the DAG. Variable labels are
stored inside membership and quantifier nodes; their magnitudes and
binary encoding lengths are uncharged. Alpha-equivalent formulas with
different names are not automatically identified. These are exact
formula-size metrics, not program bits, register instructions, compiler
states, or Turing-machine states. No state-count prediction follows.

## Exhaustive finite semantic checks

The script enumerates all 530 labeled nonempty membership structures with
one, two, or three objects: 2, 16, and 512 structures, respectively. It
compares recursive AST evaluation with separate bit-mask semantics for
the three fixed axioms DP, BU, and EPSC[Theta], and for the four matrices
under ordinary EPSC1 and both fused wrappers. All 1,590 fixed-axiom
comparisons and 6,360 schema-instance comparisons pass. Six malformed
or out-of-interface matrices are rejected.

The direct EPSC check enumerates the local subset bounds and candidate
hull extensions. Support requires the hull extension to be a subset of
the union of all relation fibers; closure activates exactly the empty
inputs and the inputs belonging to the hull. For a fused instance the
fixed repair is required only at parameter assignments whose local-bound
premise holds. A single fused instance can therefore be true although its
fixed repair is false. The retained three-object witness has member
masks [2,1,0] and the bound-variable-shadowing matrix, for which every
parameter premise is false. Both DP and BU fused instances are vacuous
there. The false-matrix instance has a valid premise, so the complete
fused schema does force its repair, exactly as the manuscript proves.

The tests deliberately do not assert that the bare repair sentences are
logically equivalent. BU holds and DP fails in the one-object structure
with an empty membership relation. The fixed gate holds and DP fails in
the two-cycle with member masks [2,1]. Their equivalence in the manuscript
uses EPSC1 resources, including the empty object, exact profile classes,
and raw Union.

No tested finite structure satisfies both the false and the
incoming-profile EPSC instances. Consequently these checks cannot be
advertised as finite models of the full unary schema or as a verification
of the consistency calibration. They validate the formula encodings and
their guarded semantics. The schema proof remains ordinary mathematics;
no proof-search engine or binary machine is implemented here.

## Independent mathematical review of the finite repair

The final no-Extensionality proof, now included in
`sections/unary_theory.tex`, from the subsection
`sec:unary-finite-exception` through the Binary Union proposition, was
read independently. The parameter budget and all transfer steps check
out. Exact full-profile singletons, the decoder and transitive covers,
raw Union, incoming-profile saturation, and the fixed purity cut use at
most one ordinary parameter each.

DP yields pure Pairing in H/Delta. After packing pure parameters into
one code, the guarded relation R(x,y;t) is locally subset-bounded in the
raw structure. Its supported EPSC1 hull has only H-members. Saturating
that hull uses only the hull as its parameter and yields an H-object.
Raw and interpreted emptiness agree on H; Delta-invariance transfers
initial closure, recurrent closure, and support. This directly interprets
full EPSC and avoids the previous two-parameter seed/filter construction.

Finally, BU applied to the one-parameter exact Delta-singletons gives DP.
In the reverse direction, the raw Union of a DP profile pair of A and B
has exactly the extension of their binary union. This proves BU iff DP
over EPSC1 without adding Extensionality. It does not prove equivalence
of either bare sentence to the other or raw deductive equivalence of
the repaired theory to unrestricted EPSC.

The consistency bridge and the canonical hierarchy construction remain
ordinary proof arguments. This code review supplies no additional
proof-assistant certificate or arithmetized machine simulation theorem.
