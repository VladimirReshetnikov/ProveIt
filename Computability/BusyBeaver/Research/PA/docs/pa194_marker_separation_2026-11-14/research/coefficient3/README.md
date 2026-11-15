# Replaying the coefficient-three refutation

From the release root, run:

```sh
python3 -B research/coefficient3/replay.py
```

Python's standard library is sufficient. Keep assertions enabled. This command
reads the retained certificate, prints a fresh receipt, and leaves the release
files unchanged. It works from any working directory when invoked by its full
path. An optional `--output /path/to/fresh-receipt.json` saves the receipt.

The expected result is `PASS`, with 73,393 primitive proof steps, 116,171
arithmetic expression DAG nodes, maximum depth 36, and final conclusion code 1.
The steps comprise 34,888 restricted-rho instances, 38,503 modus-ponens
applications, one generalization, and one fifth-head instance. The primitive
certificate SHA256 is
`baf316dce45568036fd803382b30ae2669eb504222a39a6be1f3abcad77dcb83`.

## Mathematical scope

The unchanged coefficient-three numerical calculus has the arithmetic collision
`E3(1,0) = I3(0,1) = 6`. The retained proof derives contradiction code 1 using
the four explicitly checked primitive rules. The verifier uses exact shared
arithmetic expressions and elementary Cantor-component inequalities; it uses
neither a derived K/S rule nor a propositional tautology oracle. The historical
fourteen-line proof and its generator are not required for this expanded
primitive-rule replay.

This is a refutation of that numerical calculus. It is separate from the capped
blank-tape simulations of the rejected 193-state table. No literal-machine
halting trace or newly compiled Lean proof is claimed by this check.

## Provenance and contents

The certificate, verifier, accompanying article fragment, original README, and
retained license were copied byte for byte from ProveIt commit
`793c68737d94bffa4e32a75bce6cc8058d6d22f0`, directory:

<https://github.com/VladimirReshetnikov/ProveIt/tree/793c68737d94bffa4e32a75bce6cc8058d6d22f0/Computability/BusyBeaver/Research/PA/docs/pa194nq_research_2026-11-13/search/factor3_obstruction>

`provenance.json` records every retained file's original path, Git blob SHA1,
SHA256, byte length, and unmodified status. The two documentation files have
been renamed `inherited_lemma.tex` and `inherited_README.md` to distinguish them
from this release's wrapper instructions. The inherited README discusses other
historical generation files that are not needed for this replay.

`verify_primitive.py` is the original self-contained verifier; its only
dependencies are Python standard-library modules and `primitive_proof.json`.
`replay.py` is the new thin wrapper that calls its `verify` function, checks the
expected identity and counts, and prints the result without invoking the
original script's receipt-writing entry point. Run the wrapper with `-B` to
avoid creating Python bytecode inside the release.
