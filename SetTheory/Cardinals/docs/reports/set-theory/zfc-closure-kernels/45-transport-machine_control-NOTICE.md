# Provenance and license boundaries

This is a deliberately small numerical and compiler-input subset, not a
complete clone or formal proof development.

## Unchanged third-party inputs

The upstream source is `jeff87654/busy-beaver` at commit
`297ab8df7e5de329605c3875b4934643b371a5e3`, copied through the unchanged
ProveIt vendor snapshot at commit
`61e77836565f63582561f54745f633d50efd9c7d`.

- `inputs/Prog254.v` comes from `ZF/m254/coq/tm/Prog254.v`.
  Mira-Cult designed the original machine, program, and calculus. Jeff
  (`jeff87654`) published the Coq verification and finite numeric tree.
  The file is parsed as finite data; no Coq build is included or claimed.
  No blanket upstream license was declared in the pinned repository, and
  this package does not relicense that source.
- `wade/TMBuilder.py`, `wade/tm.py`, `wade/tmdb.py` and
  `wade/LICENSE.wade` come from the corresponding files in `ZF/generator/`.
  Andrew James Wade's public backend is retained byte-for-byte under its
  original MIT No Attribution license. Framework comments acknowledge the
  NQL register-machine lineage at `sorear/metamath-turing-machines`.

## Prior work reused or reproduced

ProveIt's source-09 decoder work already identifies exact structural sharing
of the 6,459-node `Prog254.v` tree as a 203-node DAG. This package reproduces
that known representation. It makes no new priority claim for the DAG,
Wade's backend, register path semantics, original consistency machine, or
its formal proof. The new analysis/checker/assembly drivers were prepared
for the present ProveIt research request; they do not assign their authorship
to any borrowed source. Generated tables contain the unchanged third-party
backend's transition fragments and retain its lineage.

The original complete Mira/Jeff machine has 254 working states; the public
mira-emmy 253-state machine is a separate optimized table. The 265-state
Wade control in this package is neither of those tables. It has no new
end-to-end formal consistency theorem.

Exact input hashes and all generated-file hashes are retained in
`MANIFEST.sha256`. No additional blanket license grant for third-party
material is inferred from the surrounding report or repository.
