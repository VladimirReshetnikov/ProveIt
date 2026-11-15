# Bounded physical reduction research

No accepted machine with fewer than 194 working states was found by these searches.
The positive result is the exact two-shortcut acceleration proved separately in
`acceleration/acceleration_proof.tex` in the enclosing delivery.

## What changes relative to the earlier search

Earlier local quotient code normally required a replacement path to reconnect
to the original **one-step** successor. The new search permits reconnection to
any positive bounded future reference configuration. Both paths must take a
positive number of steps, and the complete finite window, head position, and
control (modulo the proposed quotient) must agree. This admits genuine
two-sided stuttering identities. It exposes 75 further neutral primary-table
row proposals and 74 further neutral proposals for the known 193-state runtime
core, beyond the earlier one-step-target pool.

The quotient screen examines pairs of working controls, redirects all incoming
targets, and synthesizes both rows of the retained control. The reference and
replacement runs stay inside the specified radius. These restrictions define a
bounded search family; failure proves no general machine-state lower bound.

## Recorded searches

| Family | Scope | Result |
|---|---|---|
| Primary PA194 | Radius 4 blank closure, radius 4 source envelope, radius 6 source envelope | No two-sided control quotient |
| Current frontier | 69 named constructions or source-validated rotations; radius 4 blank closure | No quotient or unreachable control |
| New neutral primary rewrites | 75 first-row proposals, each followed by the radius 4 quotient screen | No quotient |
| Known 193-state runtime core | 74 newly exposed one-row proposals, all 193 starts | 14,282 runs: 151 halts, 14,131 outward rays, zero remaining bounded runs, zero complete accepted source frames |
| New AX11GH/GHS | Radius 4 blank closure and radius 6 source envelopes | No quotient |

Each complete 194-control pair screen considers 18,721 unordered control
pairs. The main recorded source-envelope bounds are 100 reference steps and
200 replacement steps at radius 6. The radius 4 reference/replacement bounds
are 100/100, except the first primary blank-closure run, which used 20/100.
Exact trial counts are preserved in the logs. The manifest records the start
and its provenance for every frontier table; inferred bootstrap starts are
identified explicitly rather than being called file declarations.

The frozen source envelopes came from the existing symbolic source executor,
including its repaired collection of accelerated scan interiors. Their
receipts are included. Arithmetic-box controls are not narrowed by that
collector. These finite envelopes are search inputs, not a replacement for
the final independent source-contract proofs. Any hit would still require its
own invariant and complete blank initialization.

The ordinary blank-closure envelope itself is a sound finite abstraction:
begin with the all-zero radius window at the given start; apply each literal
transition; when the head moves, admit both possibilities for the newly
exposed boundary symbol. This overapproximates every actual blank-run window.
Every negative conclusion here is confined to the tested abstraction and
reconnection bounds.

## Offline reproduction

Python 3.10+ and a C++17 compiler suffice. Run without Python `-O`.

```bash
python3 replay.py --suite primary --out /tmp/pa-state-primary
python3 replay.py --suite frontier --out /tmp/pa-state-frontier
python3 replay.py --suite neutral --out /tmp/pa-state-neutral
python3 replay.py --suite bootstrap --out /tmp/pa-state-bootstrap
python3 replay.py --suite new --out /tmp/pa-state-new
```

The optional `accelerated-frontier` suite applies every selected exact
one-new-step shortcut and repeats the quotient search. The `fast` suite
checks the two delivered accelerated designs. Their final receipts are
recorded alongside the other logs. `--suite all` runs every suite.

The scripts use only bundled inputs and write replay output to the supplied
directory. They fail if a purported negative run yields a hit; such a hit
must be inspected, not suppressed. Reproduction times vary by machine.

## Provenance

Repository snapshot: `1e1a41f799d4658b829cdd0eabae3775a0c8c4a0` of
<https://github.com/VladimirReshetnikov/ProveIt>.

The stutter synthesizers extend the quotient and neutral-row search methods in
`Computability/BusyBeaver/Research/PA/docs/pa_sub194_research_2026-11-13/research/reduction/`.
The startup checker and its whole-frame templates are attributed imports from
that same packet. The machine tables, source envelopes, and earlier
construction code retain their original James Chang, Wade Tregaskis, and
ProveIt attributions. Relevant notices and licenses are included in `licenses/`.
The two-sided reconnection code, its new search runs, and this portable replay
driver were produced for the present investigation.

No executable check in this directory is described as an end-to-end Lean
proof of PA consistency calibration.
