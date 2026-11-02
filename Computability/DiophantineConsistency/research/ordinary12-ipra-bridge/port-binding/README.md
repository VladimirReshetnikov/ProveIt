# Manuscript-98 whole-tuple and parent-100 check

`check.py` pins the manuscript-98 provenance record and matches its recorded
`native/ACTIVE_BINDING.json` hash to the retained source69 binding. It checks
all four available compact44 payloads against the manuscript's recorded
compressed hashes and the binding's raw hashes and byte lengths. The actual
payload files used here come from the retained `ten-positive-shifted-strong`
candidate; the manuscript's own `native/ACTIVE_BINDING.json` and payload
files are absent from this checkout, so this is reconstruction against the
recorded provenance, not a fresh check of those missing copies.

The complete parent-100 operation rows, inputs, output, operation breakdown,
and degree field match the ordinary 12-variable candidate. The verified tuple
has `β=2^590069−1`, the recorded `K0=K`, `MC`, and already shifted
`MF=MF_source`, with the stated mask inequalities. The alternate
`compact44_bfs` payload has the same raw β, MC and MF but a **different raw K**:
the manuscript-bound K hash is `c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e`,
while the alternate K hash is `4364134a56b54cf132beeb9acd8e832be68f9083f4359ace4a588a1ea76a60f7`.
Substituting that K or swapping MF with MC fails the tuple check.

Normal Python actually exited 0; optimized Python was rejected. Exact stdout,
exit codes and script hash are in `observation.json`. These data checks do not
establish the compact44 internal checker/calibration, the manuscript-98
semantic proof, an iPRA derivation, or the separate 95-gate rewrite.
