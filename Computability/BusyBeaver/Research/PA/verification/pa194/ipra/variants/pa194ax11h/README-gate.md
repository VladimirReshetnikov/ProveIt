# AX11H AX-gate source window

The gate-window stage checks the revised source against the resolved primary
trie at all 34 sites from 3519 through 3552. The source steps agree at all
these sites. The model-valued runs agree for any clock whose earlier primary
controls lie in this interval. Each revised step remains in the interval or
reaches its sole exit at site 3553.

The remaining gate proofs establish termination, the register file at the
exit, and correspondence with the scheduler's AX command.

After the [candidate push stage](README-candidate.md), run the gate replay.

```sh
ax=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h
bash "$ax/check_candidate_gate.sh" "$gate_output" "$candidate_output"
```

The repository replay rebuilds the gate modules against the checked candidate
output and its recorded transitive dependencies. The generator pins the
delivered JSON files and emits the Lean source records used by the kernel.
