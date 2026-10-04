# Independent POWER12 audit

Verdict: **PASS with the explicitly pinned Pell theorem dependency**. See `AUDIT.md` for the full proof review, domain challenges, exact degrees, composition and trace ledgers, scope, and evidence limits.

Reproduce with Python 3.9+ and no third-party dependencies:

    python3 check_independent.py --source /path/to/positive-power12-continuation-20261004 --out /path/to/new-evidence

Only this independent checker runs. It neither imports nor executes source packet programs. Its output directory must be outside the source tree. It checks exact source pins and full byte/mode/mtime preservation before and after execution.

Files:

- `AUDIT.md`: complete mathematical/static verdict
- `check_independent.py`: new portable exact checker
- `evidence/results.json`: successful final receipt and check counts
- `evidence/*.json.gz`: independent exact polynomial expansions and full positive fixtures
- `evidence/source.before.json`, `evidence/source.after.json`: identical preservation inventories
- `run.log`: successful final execution
- `MANIFEST.sha256`: final audit file hashes

No new Lean build, author/upstream script, counter-machine interpreter, physical simulator, or stored schedule is executed. Finite fixtures supplement the all-input argument; they do not replace it.
