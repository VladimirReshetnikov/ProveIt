# Current thirteen-variable 178/86 scaled-norm syzygy

This separate equation has **13 strictly positive integer unknowns,
178 paid binary operations, and exact degree86**, with the complete
unchanged current2011 coefficient tuple:47,313 raw bytes /4,230 gzip bytes.
It preserves every positive zero of the accepted97/88 equation, by identity
maps on the thirteen coordinates. It has a freshly checked closed external
Lean equivalence with the actual `DiophantineConsistency.ConZFC`.

This is an expensive degree tradeoff within the current small-port,
externally formalized thirteen-variable family:81 extra operations for two
fewer degrees. It is not globally nondominated: the historical ordinary
13/88/51 and12/96/70 forms have better variable/operation/degree metrics but
separate larger compact44 tuples and proof/calibration scope. See the
[comparison-scope correction](../scaled-norm-syzygy-search/COMPARISON_SCOPE.md).
This packet proves no transfer of those older forms to current ports and
makes no internal HA/PA/ZFC, global minimum, or maintained-display claim.

## Equation and complete evidence

The [ordinary proof](PROOF.md) gives all scalar definitions. Put
`A=k−4*gamma` and `S=8*gamma*(P−1)+K*(Q−1)`. Its explicit integer-polynomial
coefficients produce

    Uc = A*(U−(A88+Bcorr)*(P−1))−Hcorr*S,
    (P*Q−1)^2+(Z−1)^2+(Uc−A)^2 = 0.

The main norm Q=1 alone forces A>0. A new zero first recovers P=Q=1 and
Z=1 independently, so both corrections vanish and cancellation of A gives
U=1. The parent residual characterization uses its auxiliary negative-unit
exclusion only after Z=1. No sign for V, canonical-only assumption, or
unconditional positive scale is used.

* [Lean source](../../Lean/DiophantineConsistency/ThirteenScaledNormSyzygy86.lean)
  proves the scale bound, complete positive-zero equivalence, ring map,
  actual MvPolynomial evaluation, and actual external ConZFC endpoint.
* [Focused checks](../../Lean/DiophantineConsistency/ThirteenScaledNormSyzygy86Checks.lean)
  expose twelve standard-only axiom reports and actual port binding, plus
  the negative scale and invalid unadjusted-sphere controls.
* [Literal graph](polynomial.json) contains every one of178 live operations:
 117 multiplications,29 additions,32 subtractions. All13 unknowns and4 ports
  are live. Its prefix is exactly88 rows of the accepted97/88 parent.
* [Independent stdlib auditor](audit.py) binds all new coefficient and
  residual formulas through complete staged sparse-polynomial identities,
  pays every gate, and verifies the entire current tuple without importing
  or executing any project or incoming program.
* [Certificate](CERTIFICATE.json) stores all178 gate degrees and their
  complete homogeneous leaders, deduplicated into137 exact polynomials.
  Uc43 has2491 terms and the full degree86 leader Uc43^2 has179146 terms.
  Every leader survives actual-port specialization, proved by a nonzero
  exact modular coefficient. The selected output coefficient is exactly
  4096*beta^54>0; it has5,103,930 bits at the actual tuple.

The norms P,Q,S are fully expanded (186/323/821 terms). Eight exact upper
homogeneous layers prove all higher auxiliary cancellations; lower layers
of the whole polynomial are not claimed expanded. The other two square
branches have actual degrees80 and72. Eight graph corruptions and nine
algebraic corruptions are rejected. Exact modular dependence witnesses bind
all17 leaves; at the actual-port positive all-ones assignment, parent/new
values576772/705109 modulo1000003 prove these are different polynomials.

## Reproduction and frozen hashes

From the repository root:

```sh
python3 Computability/DiophantineConsistency/research/thirteen-scaled-norm-syzygy86/audit.py
python3 -O Computability/DiophantineConsistency/research/thirteen-scaled-norm-syzygy86/audit.py
```

Both are read-only complete reproductions. `--write` regenerates only this
packet's graph, four coefficient copies and certificate. The auditor caps
address space at2GiB and CPU at120seconds, and requires512MiB free disk.
Normal and optimized runs do not rely on Python assertions.

| Artifact | SHA-256 |
|---|---|
| Lean source | `53be78f9046b591dcd1a33421d3dae3e14764537ac19fa0906665e3e0829f253` |
| Lean checks | `9a4b58d6ff9eddb83ce2013d18da867211b70abffac03ba9de99bbc1f82c8c4f` |
| Ordinary proof | `609fcdece2ba042a1fa0c5cf73783a8b76cda4d2238e6e1fcf1a28464bd6adf7` |
| Auditor | `4ea291f7a2680be91cd48a896ade395139fbaae5ecd8a0857636aa3be0d1535b` |
| Literal graph | `93af43ae10b9eade4e6c3377f7977c1133c33dde87104ad1f42fc3022531a180` |
| Certificate | `1e13e6970442a937db8af04ce5755839d1d2ad6446752dfccf21442657f5a507` |

The [author receipt](../../reviews/thirteen-scaled-norm-syzygy86-author.md)
and [full replay metadata](../../reviews/thirteen-scaled-norm-syzygy86-replay.json)
record fresh bounded Lean commands, all authenticated prerequisite sources
and objects, exact logs, final finite runs, and rejected author-build
snapshots. The new leaves reuse371 authenticated custom prerequisites from
the current root97/88 provider; no prerequisite/Foundation rebuild or shared
object overwrite is claimed. Independent acceptance remains separate from
these author checks. Frozen parents, exploratory packets, and the page
remain unchanged.
