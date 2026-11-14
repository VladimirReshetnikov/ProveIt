Cached symmetric Shift with no-push MP and radix-six constructors
================================================================

This folder preserves a previously performed composition experiment, not a
new accepted sub-194 result. It has 203 raw controls and eight simultaneous
folds, resulting in a physically verified 195-working-state table.

The state accounting is

    136 fixed controls + 67 AX readers - 8 folds = 195.

The natural extra folds 41 -> 99 (the radix-six construction) and 41 -> 331
(the cached symmetric-Shift construction) both remove native control 41.
They therefore cannot both be counted as separate state savings. The supplied
finite one-history-bit fold census contains nine opportunities but a maximum
matching of eight. This does not exclude a different fold or construction.

The original observed verification checked 4,872 source outcomes over 3,772
source sites, 32 simultaneous local fold cases, and the entire blank startup
to the canonical source frame after 57,760 transitions. A fresh deterministic
replay of those same checks is recorded in receipt.json. It is not a new search.

    python3 -B verify.py

Python 3.10+ and the standard library suffice. There is no network or checkout
dependency. To write a separate replay receipt, pass --receipt NEW_PATH.json.
Assertions must remain enabled.

recorded/machine195.native.tm is the exact retained table. Native start is 74
and halt is 254; the halt control has no outgoing rows. Its 390 rows use
state/read/write/L-or-R/next notation. recorded/nodes.json and instructions.json
bind its source construction. The other baseline inputs and compiler/runtime
modules are included. original_combine.py preserves the original experiment
entry point; verify.py checks the delivered files and avoids overwriting them.

Proof and reproduction limitations
----------------------------------

The source simulator uses inherited arithmetic-block summaries after checking
that the relevant literal rows remain unchanged. The generic blocks were not
independently rederived for this composition in this experiment. No new
end-to-end Lean/Rocq consistency proof or state-count lower bound is claimed.
The mathematical logical calibration is inherited, and this folder's purpose
is the exact reported physical composition evidence, not a new logical theorem.

Inputs were read from ProveIt commit
317b07268681b44ff352d173a162e2a8c241b2fe, notably the radix-six raw machine,
the primary PA194 grammar/folds, and the PA194NS cached-Shift source patch.
The two added helpers have distinct native labels 330 (radix) and 331 (Shift).
Original notices are retained under licenses. Local hashes are in MANIFEST.json.
