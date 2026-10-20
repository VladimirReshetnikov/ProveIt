# Two independently constructed decoder allocations

`portable/certificates/binding_candidate0001.json` is the original independent
decoder audit. It binds the allocation reconstructed directly from the literal
machine and source, now retained as
`verification/independent_decoder_allocation.json` (SHA-256
090117653c79fece4d648c93e1e73cf74bc93d4ae75de513a9e8dcb362699797).
It is not a receipt for `portable/inputs/allocation.json`: the two allocations
use different internal tree-node identifiers. The source and machine hashes are
identical, and both describe the same 185 source nodes and 13 shared state roles.

The deterministic constructor copies `portable/inputs/allocation.json` into its
output. The unified replay freshly checks that exact allocation in phase 04;
`verification/constructed_decoder_binding.json` preserves the passing receipt
from the release replay. Thus the original independent audit and the constructor
allocation audit are both retained, with their distinct input bytes identified.

To replay the original independent allocation audit from the packet root:

    python3 -B portable/verification/check_decoder_binding.py --source machine/sites221.json --allocation verification/independent_decoder_allocation.json --table machine/k221.native.tm --output /tmp/k221-independent-decoder.json

The normal `portable/reproduce.py` command automatically checks the constructed
allocation. Neither audit substitutes for primitive runtime or blank startup.
