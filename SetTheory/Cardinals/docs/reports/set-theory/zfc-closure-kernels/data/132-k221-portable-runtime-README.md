# Exact 221-state runtime and source certificates

These are the runtime components of the top-level portable replay. Prefer running `../reproduce.py` with an external empty output directory.

For a separate direct replay, supply an input directory containing native `candidate.tm` and `sites.json`, and an external output directory:

    python -B verify221.py INPUTDIR OUTPUTDIR
    python -B audit221.py OUTPUTDIR
    python -B generate_invariants221.py OUTPUTDIR
    python -B -O check_invariants221.py OUTPUTDIR

The exact input hashes, 221-state census and 442 transition rows are checked before replay. Native labels start at 0 with terminal 254; canonical labels are a separate explicit bijection. Assertions must be enabled for the fresh symbolic runtime engine. Both independent audits retain their explicit checks under Python optimization.

All 6,167 guarded source cases are proved for nine independent arbitrary natural registers, arbitrary extra gap and arbitrary nonempty finite spare lists. Blank startup is executed with two independent tape representations and the entire nonblank support is compared. Source fixed-point invariants are separately regenerated and independently checked.

`reference_results` contains completed outputs of the exact packaged verifier, not discovery-driver receipts. The top-level default regenerates them externally; its quick mode checks their integrity instead. Neither mode infers mathematical-calculus adequacy from runtime checks.
