# Exact prefix250 marking

`RegisterMarkPrefix250.lean` ports the marking excursion to the exact 250 table. It proves all nine selector entries, erasure of the selected unary one, and return in exactly `2*width(pre)+3` steps, using old 2 for physical register 0 and old 6 otherwise. Every register value, finite left context and following spare suffix is arbitrary.

`mark_word` and `mark_with_suffix` permit an arbitrary terminal word. `mark_zip` and the Core `mark` theorem use unpadded register files, matching the new prefix-carry boxes. The output preserves the whole tape and changes only the selected ordinary 01 header to 00. The generic return scanner is instantiated with the new machine's literal rows; no old 252 execution theorem is assumed.

The root's second attempt passed the 165-line source and focused audit, with 8 standard-axiom probes, 4 callers and no warnings. The first attempt already passed the identical source, then failed one audit caller because its simplifier left `if True`; adding `if_true` repaired only that caller. Both attempts and their fresh-before-audit objects, raw source/audit/guard snapshots and outputs are preserved. The second attempt compiled both units again; it is not described as an audit-only continuation.

Successful record SHA256: `5140723f74774c3cce3fa38eee2c8fd0d61d4382cacda3d6078c05bc0695b6d6`.
Fresh object SHA256: `778cf0e4c2ca8b7b54391d0848a9dfa4839f8a53315296506d380dce6ae0ab98`.

The bounded checker reuses seven exact project providers and the supplied Init/Omega boundaries, builds only the marking source and audit, and records the fresh object before the audit. Both commands use one thread, 4096 MiB and a shared 120-second budget with default proof limits. Prepare-only invokes neither compiler nor version query:

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_prefix250_mark.py \
  --repo "$PWD" \
  --table-evidence Computability/BusyBeaver/Research/ZFC/results/table-prefix250-verification.json \
  --output /tmp/prefix250-mark-fresh-preparation --prepare-only
```

Mira-Cult, Jeff Ketchersid and Wade retain the original marking/machine/compiler attribution; the port uses the maintained Lean proof of the public Box.v contract. This local theorem does not prove full instruction simulation, bootstrap, consistency equivalence or PA-internalization.
