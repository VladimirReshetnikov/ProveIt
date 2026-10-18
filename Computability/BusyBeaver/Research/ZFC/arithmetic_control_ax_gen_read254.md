# Internal AX constructor and cache read, controls 41–136

`ArithmeticControlAXGenRead254` composes the checked GEN prefix with the following
cache read at their literal control 122 boundary. In every model of IΣ₁, for every
internal encoded register file with S1 and S2 initially zero, a positive internal
runtime takes catalogue control 41 to control 136 with these complete-file updates:

- `TW := wal oldP1 oldCache`;
- `WS := cantor oldTW oldWS`;
- `cache := oldCache + first(oldPL)`;
- `PL := second(oldPL)`.

The other five coordinates are preserved, including both scratch registers.
In particular, TW uses the original cache, before the following read adds to it.
The paired-stream client substitutes arbitrary internal `x` and `rest` when
`oldPL = cantor x rest`. No zero-cache, bounded-value or formula-wellformedness
premise is added. The proof composes existing internal run contracts; it introduces
no new induction. These control numbers index the shared register interpreter.

The immediate parents are the [GEN constructor](arithmetic_control_gen254.md) and
[AX cache read](arithmetic_control_ax_read_cache254.md). This unit closes their
41→136 composition. The rest of AX, its comparison with Enum, and the arithmetic
binary-machine consistency endpoint remain separate obligations.

The selected third attempt passed nine named axiom probes and eleven typed callers,
with zero warnings. The finite join uses no axioms; the eight arithmetic statements
use only `propext`, `Classical.choice` and `Quot.sound`. Source and audit took
2.565042 and 2.250851 seconds under default Lean proof limits, one thread and a
4 GiB memory limit, with a shared 120-second deadline.

The strict guard checks 104 project source/object pairs, six retained external
provider pairs (five actual direct import boundaries), and Init/Omega. Both
immediate parents have recorded pre-audit source-object and first-provider
identities. Older ancestor evidence retains its recorded limitations. All 239
current inputs were rehashed; the new source object was captured before the audit
and checked again afterward.

- [Actual verification](results/arithmetic-control-ax-gen-read254-verification.json)
- [Existing-evidence review](results/arithmetic-control-ax-gen-read254-review.json)
- [Publication bindings](results/arithmetic-control-ax-gen-read254-publication.json)
- [Exact history](results/arithmetic-control-ax-gen-read254-history.json)
- [Original source-only provider proposal](results/arithmetic-control-ax-gen-read254-provider-proposal.json)

History preserves both failed source compilations and their raw logs. The first
attempt unfolded the intermediate file before applying preservation lemmas and
reported two unused simplification arguments. The second applied those lemmas in
order but left the final definitional equality unclosed. A final `rfl` closed that
residual in the selected source. Neither failed attempt reached the audit. The
theorem statements and audit remained unchanged. Separate independent source/API
and repair reviews are retained; the final evidence reviewer authored the source,
audit and guard, while root independently read them and executed every attempt.
Original inventories and the provider proposal retain their initial source-version
identities; the selected source, guard and actual record are identified separately.

With the recorded caches available, run from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_gen_read254.py \
  --repo "$PWD" --dependency-root /home/codex/src/Proofs \
  --gen-evidence "$PWD/Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-gen254-verification.json" \
  --read-cache-evidence "$PWD/Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-ax-read-cache254-verification.json" \
  --output /tmp/ax-gen-read254-recheck --prepare-only
```

Use a fresh output directory for each invocation. Omit `--prepare-only` for the
source and audit compilation. Preparation invokes no compiler or version query,
download or dependency build. The packet contains exact source and textual
history, with historical cache prerequisites; it does not attest a fresh rebuild
of the dependency closure. Maintained default preparation is recorded separately
after installation. Existing attribution to Mira-Cult, Jeff Ketchersid and Wade
is retained through the interpreter and its checked parent modules.
