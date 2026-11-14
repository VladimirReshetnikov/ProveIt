REJECTED RESEARCH TABLE — NOT A CONSISTENCY-MACHINE CANDIDATE

The file rejected208.native.tm is the failed two-rotation shortcut from the
Joint U209 baseline: rotate 155/85 and 52/154, then identify 154 with 85. It has 208
working labels but fails the declared interpreter contract. The exact failure
is already discussed in the supplied newer U208 reports; this copy is a
reproducible regression example, not a new accepted construction.

Reproduce from the release root:

  python3 research/rejected_rotation/check_prefix.py \
    baseline/snapshots/u209_joint/native.tm \
    research/rejected_rotation/rejected208.native.tm

The checker runs 17 literal transitions from dispatcher 84, head 0, with known
left marker 1 and prefix 0011001000001. It rejects any read outside those cells.
The parent reaches state 42/head 13 without changing tape; the rejected table
reaches state 25/head 13 and changes cell 12 from 1 to 0. This refutes the prefix
contract and does not determine eventual behavior from the blank tape.

The file is deliberately named rejected. Do not combine it with the valid
172/211 fold and report the resulting 207 labels as a verified saving.
