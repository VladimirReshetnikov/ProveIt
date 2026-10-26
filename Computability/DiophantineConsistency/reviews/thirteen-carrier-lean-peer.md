# Independent review of the literal thirteen-coordinate Lean carrier

Reviewer: `/root/circuit_reduction`. The author of the reviewed new Lean
module and checks is ROOT. Verdict: **PASS within the local arithmetic
scope stated below**. No source correction was requested or made.

## Frozen sources

Paths are relative to `Computability/DiophantineConsistency/`.

| File | SHA256 |
| --- | --- |
| `Lean/DiophantineConsistency/ThirteenCarrier.lean` | `2f19e9690841d15d48a281cfafd8813270e0dcfe38a9f6c68ab9d2f9d85453ca` |
| `Lean/checks/ThirteenCarrier.lean` | `556c29edd79ff619a929df7f578846bf53ce9e1c4938a0c7e9496e1f1cefbddd` |
| `Lean/DiophantineConsistency/ShortEquation.lean` | `2d447a166a33dedb90c8acdf0755d584a9d057bf46a047e0a454bf150f628b68` |
| `research/thirteen-variable-independent/PROOF.md` | `d2e40a04fdc670a5f5a05d2c8e7e762e07ef559eb051e5ff6f5c82e7e3e8f6a8` |
| `research/thirteen-variable-normalized-independent/PROOF.md` | `22670c2f7c35a9e0b88b9505620c924f2a867922cb62464bee0bcf54f752529d` |
| `research/thirteen-variable-independent/polynomial69.json` | `3400069ead0bbf7b85d382c47fdd790bc18d68d9979e049f475d4e1c52d4182f` |
| `research/thirteen-variable-independent/polynomial70.json` | `b36b1b4fa645b772d5cafe82a0359eca264e228114cacd2fcce6da902b2eac82` |
| `research/thirteen-variable-normalized-independent/polynomial.json` | `50c7d99e5a1abb19f83c9c3b243995d965ecb3d1d39d509d13fd3b18dcec95d4` |

I read the complete 161-line new module, complete 18-line checks, all of
the imported local `ShortEquation` support, both ordinary proofs, and
every row and coordinate declaration of all three literal graph files.

## Literal formula and coordinate review

The independent coordinates are exactly
`J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma`, in that order. In particular,
`i=v4`, `T=v5`, `s=v6`, `w=v7`, `n=v8`, `eta=v9`, `zeta=v10`, and
`m=v11`; the old independent `z` and `y` are absent. The four port
coordinates are `beta,K,MC,MF_source`. The rank uses `p2 + q*p3` and
introduces no additional beta shift into the source mask.

The full common arithmetic agrees with the retained graphs, including
`tau=E*n+k-R`, `V=f^2*(c*T-R)-c`, `G=(K+w)*C-F`, and the signed
abbreviation `y=1+4*(b*(m-V^2*G)-G)`. The core's `t=b*i*c^2` is the
unscaled strong ordinate; consequently `Delta*t` is precisely the old
`S=b*i*Delta*c^2`. This distinction is essential in all three values.

After the graph's display-name translations (`B` to `G`, `N0/N1` to
`P/Q`, and `qm` to `b`), the entire outputs are:

- `value69=P*Q*((Delta*t)^2*(V^2-y^2)+y^2)*
  (Delta*f^2-(Delta*t)^2)-Delta`;
- `value70=P*Q*(Delta*(f^2-1)*(V^2-y^2)+y^2)*
  (Delta*f^2-(Delta*t)^2)-Delta`;
- `value71=P*Q*(Delta*(f^2-1)*(V^2-y^2)+y^2)*
  (f^2-Delta*t^2)-1`.

These match all three complete graph formulas. Associating `E*k*Y`
as `E*(k*Y)` and commuting the factors of `S` changes no polynomial.
The generic ring-map lemmas and `MvPolynomial` evaluation theorems
bind these literal values to actual polynomials on `Fin 13`.

## Mathematical strength and hypotheses

The complete identity `value70=Delta*value71` is proved over any
commutative ring. Over integers, its zero-set equivalence requires only
`Delta != 0`. The 69-to-71 theorem additionally uses the proved
negative-unit obstruction for discriminants `(a+2)^2-1`; it applies
`ShortEquation.scaled_zero_iff_reduced` with `m=P*Q` and the actual
signed `y` and gap. There is no assumed sign for `y`, `V`, `G`, `C`,
or `R`, and no assumed auxiliary-norm equality or canonical witness.

For positive inputs and `beta>0`, the module derives `a>0` and
`Delta>0` before assuming any of the three polynomial equations. Thus
`positive_polynomial_zero_sets` proves equality of the entire positive
zero sets under the identity on all thirteen coordinates. It does not
need the stronger native port boxes. This matches the normalization
and coefficient-replacement arguments in the ordinary proofs.

The focused checks bind the actual `t` coordinate symbolically and
verify a negative derived `y` with every independent coordinate
positive. Their small port tuple is a formula check, not an assertion
that it satisfies the native port box or any consistency theorem.

## Fresh verification and boundary

The reviewer freshly ran, successfully:

```text
lake env lean Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenCarrier.lean -o /tmp/ThirteenCarrier-peer.olean
lake env lean Computability/DiophantineConsistency/Lean/checks/ThirteenCarrier.lean
```

A separate temporary axiom report also checked `scaled_identity`,
both integer zero-equivalence theorems, and
`positive_polynomial_zero_sets`. The ring identity uses only
`propext` and `Quot.sound`; the equivalence endpoints use only
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, custom
axiom, or `native_decide` occurs in the reviewed new sources.

These are fresh checks of the new module and checks against the existing
dependency closure, not a claim of freshly rebuilding every ancestral
module. The graph files were read and matched as complete formulas;
this receipt does not claim a new Lean proof of their operation counts
or degrees. The labels 69/174, 70/140, and 71/128 identify the retained
arithmetic profiles. The fresh-seed existence map, native calibration,
the concrete port materialization, and an internal-ZFC consistency
endpoint remain separate formalization obligations. No such endpoint
is assumed or proved by this local zero-set result.
