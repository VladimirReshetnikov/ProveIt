# Preliminary same-provider saturation closure

`scan.py` records current source hashes and declared import order for the
modules absent when importing `ArithmeticSaturation` and
`ArithmeticMaskPopulation` on the independently audited free-J population
provider. At this observation the two sides contained the same 109 `.olean`
paths and matching hashes; the source-declared missing closure comprises
`ArithmeticBinaryCarry`, `ArithmeticSaturation`, `ArithmeticRepunit`, and
`ArithmeticMaskPopulation`, in the recorded topological order. The audited
population-client receipt is pinned. The isolated scan exited 0 and an isolated
`-O` scan was rejected with exit 1.

This is a point-in-time source and object observation, not a simultaneous
source freeze, build, complete package/dynamic ancestry audit, or PRA proof.
A proposed replay must freeze the four sources and client, validate all
same-side inherited and source hashes, verify each direct import, rerun the
parent artifact audit, record compiler logs and exits on both sides, and use a
reviewed resource monitor with its sampled-process limitations. The proposed
graph client is an explicitly uncompiled draft in
`free-j-saturation-client-prototype`.
