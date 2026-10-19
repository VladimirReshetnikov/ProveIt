# routing245-d47

This is a new **245-state** binary blank-start table with source depth 47.
It does not reduce the working-state count. The halt state is separate.

- Canonical table: `certificate/machine.tm`, start 0, working states 0..244,
  halt 245, SHA-256
  `1c29e7659b916c0cb31d26c26e73d08f0e3e7f6444560788ec554135aecbea85`.
- Original labels: `certificate/machine_old.tm`, start 95, dispatcher 96,
  halt 254, SHA-256
  `e074e5349e32c9290625805dcae155610991fba9e4a7d61039c9bda5a2ca80ae`.
- Exact renumbering, grammar allocation, logical/physical instruction sites,
  source bisimulation and blank tape are in `certificate/`.
- Independently derived actual-table macro inductions are in `runtime/`.
- `frame-composition.json` records the independent successor-frame audit.
- `whole-frame.json` records the fully expanded unbounded-register proof:
  8,391 cases, 2,239,582 symbolic rules and all 490 literal transition rows.

The generator and frozen recovered grammar are in `../trace_work/`; the
unchanged compiler and source semantic theorem are in the pinned reference
archive. Use the root `code/verify.py` to replay the complete composition.
This has the same ordinary-proof status as the baseline; there is no new
closed Lean or Rocq endpoint for the changed table.

