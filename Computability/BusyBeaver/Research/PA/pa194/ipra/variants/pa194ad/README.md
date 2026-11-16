# PA194-AD table and register allocation

The [delivered PA194-AD table](../../../../docs/pa194_conpa_2026-11-13/construction/tables/pa194_AD.tm)
has 194 working states and swaps the physical A and D registers. The table
SHA-256 is `27613aa92da79ba2ec6e2e88e0ac909fda218e06495ecc0af27201eac0e26c8f`.

- [`PA194ADTable.exact_table`](PA194ADTable.lean) checks the 388 rows against
  the primary table. Only dense row indices 219, 221 and 249 change, affecting
  the targets of the read-1 transitions at native controls 161, 17 and 144.
- [`PA194ADTable.run_eq_until`](PA194ADStep.lean) proves equality of the
  finite runs from any shared configuration as long as the primary run has
  read none of those three rows. It uses the existing primary semantics via
  [`primary_next` and `primary_run`](PA194ADBounded.lean).
- [`PA194ADStore`](PA194ADStore.lean) transports register access, single-register
  updates and tests under the A/D swap for any register value type.
- [`PA194ADFile`](PA194ADFile.lean) and [`PA194ADFrame`](PA194ADFrame.lean)
  transport the packed register file and the encoded source frame for
  arbitrary values in PRA models. They preserve the spare register and suffix.

The physical simulation across the changed rows is still needed for the
halting equivalence and the derivation in iPRA.

Run from the repository root with a fresh output directory.

```sh
dir=Computability/BusyBeaver/Research/PA/pa194/ipra/variants/pa194ad
bash "$dir/check.sh" /dev/shm/pa194ad-replay
```

The checker pins both delivered tables and label lists, regenerates the
primary row data, verifies all companion row literals, and builds the
proofs in one output directory. It uses the retained primary scheduler
dependency path, which can be passed as the second argument.
