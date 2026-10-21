Offset two-adic pairing experiment
=================================

Codec: P2(a,b) = 2^a (2b+1) - 1.

Run from the packet root:

  python3 -B experiments/two_adic/reproduce.py --output-dir replay/two_adic

Only the Python standard library is needed.  The default baseline is
encoding/inputs/k219.sites.json, verified by its pinned SHA-256.  An
alternative local pathname for those exact bytes can be supplied with
--baseline-source.  No Git checkout or ancestor archive is required.

The program reproduces 644 finite helper checks, the non-additive-output
witness, and all four full source reconstructions with exact source costs.
It writes their source-site JSON, new helper ASTs, and summary.json to the
selected output directory.  The checked receipt from this investigation
is receipts/summary.json.  Assertions must remain enabled (no -O or -OO).

comparison.tex is an include-only section for the main report; it uses
the main report's existing \file macro.  It states the all-natural codec
and helper arguments, costs, and outstanding obligations.  Neither the
one-sided measurements nor the matched replacement is claimed as a
calibrated consistency program.  No binary TM was compiled for this trial.
