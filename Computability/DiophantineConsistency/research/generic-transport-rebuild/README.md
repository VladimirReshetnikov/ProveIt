# Generic carrier transport rebuild

This packet freshly checks three generic transport helpers without the
unrelated historical `Direct80RankEquality` import. Compared with the
retained historical source snapshots:

* `TransportOrder.lean` deletes only `import Direct80RankEquality`; its
  `Mathlib.Tactic.Linarith` import and proof body are unchanged.
* `CarrierTransport.lean` adds direct imports of
  `ArithmeticGcdNormalization` and `ModelDifferenceRing`, supplying the
  model notation and difference-ring facts formerly available transitively.
  Its proof body is unchanged.
* `OffsetBound.lean` is byte-identical to its historical source.

`run.py` compiled these three modules sequentially from fresh source into
`/tmp/generic-transport-ufzumibs`, enforcing 8-GiB/two-process resource
guards and pinning source bytes, Lean, selected arithmetic/model/tactic
providers. Accepted `observations/attempt01/` records PASS with actual outer
command exit 0. The objects are:

* `TransportOrder.olean`: `6696792c784a1f6dc56e06076350015ca235a8973caf3ecda2a9328128056da2`;
* `CarrierTransport.olean`: `05b15e987fa4eeb289936785ac2aaf7d4d2b0916fe29fd44ad9d52402c9da53d`;
* `OffsetBound.olean`: `1702af9273f8d0211bc57a013b97fe58c7e58a0791bb4b217f1207c6a27923a4`.

The historical source snapshots are `/tmp/tenpositive-transport-order-wpjgqf72/TransportOrder.lean`
(SHA `a72bc5ad47a0188de95ea12713ea6d273375c6c81233d6f8720d5099579d9723`),
`/tmp/tenpositive-carrier-transport-r9_49vrn/CarrierTransport.lean`
(SHA `15b76092ae7172e11b07735a918fec18051df29ba54e68f36939a8a47883e990`),
and `/tmp/tenpositive-offset-bound-v3g8qedt/OffsetBound.lean`
(SHA `696900c026b495235e88def39125f56b774341f1ed6ddd5aaccc5a9d0080525b`).
This generic helper build is not a trace75 transport sign, halt or iPRA
result. Direct external providers are pinned, but the runner records earlier
stage object hashes without separately rehashing them before each later
stage; between-stage stability is not independently established. Project and
package transitive, historical source/object and dynamic ancestry remain
inherited; no full closure scan or independent replay is claimed.
