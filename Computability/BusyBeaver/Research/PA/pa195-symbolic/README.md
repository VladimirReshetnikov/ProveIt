# PA195 symbolic source-frame contracts

`PA195Symbolic.lean` gives a reusable contract format and proves that, for any
machine with the imported M6 register-box lemmas, a kernel-checked successful
symbolic execution yields positive physical reachability for every valid
complete register file and gap. For frame targets, normalization identifies
the exact full physical endpoint. The generator reads the hash-pinned
`source.json` from the original PA195 archive, expands each decrement into
its zero and positive branches, and emits batches of explicit Lean contracts.
Lean itself executes every generated test against the exact unfolded parent
table and proves each batch by kernel reduction; it does not trust the Python
symbolic-executor outcomes.

From the repository root, the following command checks all 3,700 listed
sites (4,815 symbolic branches) sequentially, in batches of ten source sites,
using a temporary `/dev/shm` directory:

```sh
Computability/BusyBeaver/Research/PA/pa195-symbolic/check.sh
```

For an independently reproducible smaller check, pass a half-open range:

```sh
Computability/BusyBeaver/Research/PA/pa195-symbolic/check.sh --start-site 0 --stop-site 10
```

`generate.py` accepts archive/member/hash and Lean engine/machine names to
support compatible candidate packets. Its current input adapter expects the
original packet's site-record format, nine-register mapping, 48-cell frame
convention, and native halt control 254; other formats need their own checked
adapter and machine-engine binding.

The Lean proofs certify the emitted contracts, not that the JSON paths and
successor ordinals coincide with the actual source tree and compiler. That
source-graph binding remains a separate obligation. Nor does this prove all
machine/source execution traces correspond, or establish a PA, PRA, or iPRA
consistency equivalence. A generated count is not a record that all batches
have completed; the verification status is recorded separately after a run.
