# Expanded compact/iPRA rebuild: stage 341 exact-warning retry

The rejected attempt emitted one unused simp argument warning. This retry
keeps the source unchanged and accepts only the complete, source-pinned
warning log after path normalization. Five mutation checks reject added,
missing and altered warnings, an added error and an added `sorryAx`. This
exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and rejected direct dependency guards. It quarantined
the rejected object and rebuilt the unchanged source. Lean exited 0 in 20.728
seconds; the exact warning verifier and final guards passed at 341/425, with
source and direct dependencies unchanged. Retry and quarantined object
SHA-256s both equal
`e693b994b600f5e5ca918db6fa588850dc5469309e12d0982d40278741b6f391`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `a480a6db90cafe5fa1783e12991ca067948120cff79633e2b11568791d48c762`,
`d3a05920dcd46e15d63c67aa964c1b049d0c8e55c0ca9716fbcb7840fd9efd5b`,
`6736ec226d5a4658d04a5e754200fdb6c62fa65656af399d3ae215278605ae85`,
`925c591c21395f2d98443a8677783ada7dee6bede67c122c06ec5fa0b55f2f81`, and
`7582ed4b2894144f4c56ec66757380918db4b40ae503a98abfca388158817bdb`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,330,272 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
84 stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated.
