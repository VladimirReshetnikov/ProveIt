# Independent source review of the 88 signed early-index theorem

The stated conclusion of
[`graph_signed_early`](../../research/ordinary12-absorb88-signed-early-index-draft/Absorb88SignedEarlyIndex.lean)
is consistent with the source-level proof and its stated assumptions.
This review did not run Lean, replay the proof, or authenticate transitive
provider objects.

The theorem assumes an indicated IΣ₁ model, four **standard natural**
ports, all twelve witness coordinates positive, positive cast first port,
and an actual zero of the displayed 88 graph. It additionally assumes the
strict negative-transport inequality `ιBp < ιBn`. The conclusion constructs
an internal natural Pell index `n≥2`, identifies `k` with the doubled
Pell ordinate, and proves in the model difference ring

```
q⁴ ∣ 2n − rank − 1.
```

The branch inequality is a hypothesis; this theorem does not prove that
every 88 zero satisfies it. The rank is a signed difference-ring
expression and is not asserted nonnegative. The conclusion is a
congruence, with no rank window or equality `2n=rank+1`. For example, at
the level of this divisibility alone, `q=2`, `n=2`, `rank=−13` makes the
dividend 16 while the rank is negative; this numerical illustration is
not asserted to be an actual graph zero.

The source argument uses the imported first Pell-root norm and
`solution_residues` to obtain `k=2n+4P*s`, with `P=XY²`. The imported
actual-graph gap gives `k≥8P+4>2`, and strict growth of the represented
Pell ordinate yields `n≥2`. The chart definitions give `q⁴∣P`. The
imported signed rank theorem supplies `q⁴∣k−rank−1`; subtracting
`k−2n`, itself divisible by `q⁴`, gives the displayed result. This review
does not independently reprove those imported results or their model
foundations.

The source SHA-256 and the hashes of the output object and two direct
input objects match the values reported in the theorem packet. The
read-only digest check below exited 0 and produced
[`result.json`](result.json):

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/absorb88-signed-early-index-independent/review.py
```

Those object paths are temporary. Hash agreement is not a source-to-object
or transitive ancestry proof. The cited theorem packet reports an observed
Lean exit 0 and `[propext, Classical.choice, Quot.sound]`; this review
did not independently observe that process or rerun Lean.

```text
8ce2dec47bfdb71c7256adaf02f52d5466cfcf48085885e017319c50e0380e67  review.py
0b357b60e90b9345482da30ed73c7da1c8baff9e5aea859fc5f9ca0f2d0f17ba  result.json
```
