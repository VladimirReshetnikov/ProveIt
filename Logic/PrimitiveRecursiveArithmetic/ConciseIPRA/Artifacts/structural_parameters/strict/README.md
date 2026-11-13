# Three strict checker refinements with shifted coordinates

This secondary package implements the existing native scalar iPRA calculus.
It changes the syntax encoding and certificate implementation, not the
arithmetic axioms. The controls are exact copies of the ProveIt sources at
commit `0198424b74acc33db20c5180c8019ecd7d14a75a`.

## Result and exact limitation

| Complete checker | Significant tokens | AST nodes | Normalized bytes |
|---|---:|---:|---:|
| `checkers/strict_tokens299.py` | 299 | 343 | 633 |
| `checkers/strict_ast335.py` | 308 | 335 | 667 |
| `checkers/strict_bytes583.py` | 310 | 361 | 583 |

The componentwise envelope is **299 / 335 / 583**, attained by three different
programs. The pinned repository's current strict envelope is **302 / 340 / 584**.
The comparison permits the explicitly described change of public encoding.
There is no claim that one program beats all three strict coordinates, and
none of these programs beats the compact extrema **239 / 255 / 460**.
The compact and strict contracts differ. These source sizes are achieved
upper bounds, not proved complexity lower bounds.

Each checker reads one whole JSON input, validates that its entire parsed
input consists of exact integers and lists, validates the public sorted Eq/D
goal grammar described below, and prints `ACCEPT` only after a successful
finite check. Ordinary and optimized (`python -O`) execution use the same
acceptance policy. **Completeness is for canonical native encodings.** The
validated grammar also admits noncanonical aliases; it does not imply that
every grammatical spelling with a provable reading has a certificate.

## Reproduction

Run `python3 run_all.py` from any directory. CPython 3.12.14 reproduces the
recorded size convention. The script checks the controls' hashes, verifies
the exact source transformations, measures the complete modules, and executes
controls and candidates against fixed positive, false-goal, witness-capture,
and malformed-input fixtures. There are 63 cases for each protocol and three
control/candidate pairs, each executed normally and with `-O`: 756 executions.
The results are recorded in `measurements.json` and `validation.json`.

Finite tests support the implementation claims. The correctness argument in
`PROOF.md` uses the pinned repository's established mathematical bridge; it
is not a new mechanized proof of that bridge or of Python execution. A local
interpreter can run out of stack, memory, time, or allowed integer digits.
Mathematical completeness concerns finite successful computations with no
fixed resource cap, as in the inherited presentation.

## Input formats

The final item of the top-level JSON list is the goal. Earlier items form a
stack consumed from the end. Unused prefixes are permitted, but the whole
input alphabet test also checks them. Every recursive call consumes a packet,
including calls that close at a terminal.

The token and AST profiles read three-field records `[s,u,t]`. They infer and
recursively check the major premise of a transport or specialization when
the endpoint matches. The byte profile reads four fields `[s,u,t,m]`, with
an explicit major `m`. These are distinct protocols. Progress uses the literal
mode `u=2` and requires a binary equation matrix; cases use `u=[]` or `u=0`.

All three use the new repository's global entry-reservation schedule: scan
the goal at the old floor, reserve one negative name, form the witness
preimage, then check the major before using its returned floor as the fresh
discharge parameter. The schedule and evaluation order are unchanged here.

Fixtures are stored in the unshifted source encoding. The runner adds two to
each integer coordinate at least three, recursively through lists, leaving
negative parameters and control values zero, one, and two unchanged. For the
four-field candidate it also replaces an empty administrative major `m=[]`
by scalar zero. The source byte control's initial neutral is the empty list;
the shifted target's initial neutral is scalar one. Both read as truth.

For an example, run:

```sh
python3 checkers/strict_tokens299.py < examples/three_zero.json
python3 checkers/strict_ast335.py < examples/three_zero.json
python3 checkers/strict_bytes583.py < examples/four_zero.json
```

## Public grammar and canonical restriction

Read the public goal at depth 2. At a list of arity r, require
`r in (1, 2 + d % 2)` and read every child at depth `d + 5 - r`.
At a scalar require an odd depth, an odd scalar, and `0 <= a < d`.
Formula positions therefore admit equality and the paired binder D; term
positions admit successor and the iterator. Auxiliary ternary closure Q is
available inside certificates. Closed public goals contain no negative rigid
parameters. The alphabet gate rejects floats, booleans, strings, objects,
and nulls even when they occur in an unused prefix.

Canonical zero is `1`. Canonical slot j has coordinate `5 + 2*j`, replacing
the old `3 + 2*j`; canonical expressions do not refer to dummy slots introduced
by arithmetic constructors. The new parsed grammar additionally admits zero
aliases such as scalar `3` and references to those dummy slots. Soundness
concerns every accepted input, while completeness is limited to the canonical
representation of the native theorem set.

This qualification is substantive. The pinned repository's
`composition_and_dummy_slots` package exhibits the grammatical old code
`[[5],[1]]`, whose all-dummies-zero reading is S(0)=S(0), but which has no
certificate in the studied raw protocols. Its shifted spelling is
`[[7],[1]]`. Thus a grammar check must not be described as a complete decision
procedure for all aliases with the same ordinary reading. This issue does
not affect canonical encodings or the inherited native-calculus/iPRA bridge.

## Controls and provenance

The files in `controls/` are byte-for-byte copies of the following paths under
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Artifacts/scope_phase/code/`:

* `checker_entry_tokens304.py`
* `checker_ast340.py`
* `checker_bytes584.py`

The matched entry-control envelope is 304 / 340 / 584. The repository's
302-token record comes from its separate return-reservation profile, which
is not the direct source of the new 299-token checker. This package's three
candidates all retain entry reservation.

Positive fixtures were compiled from
`checked_reduction/native/fixtures/strict_cases.json` using the pinned
`scope_phase/code/compile_direct_three.py` and `compile_four_entry.py`.
The fixed resulting certificates, false-goal mutations, malformed values,
and entry-reservation witness-capture diagnostics are included. They can be
checked without importing a compiler or any other repository file.

`PROVENANCE.json` records the controls' repository paths, commit, Git blob
identifiers, and SHA-256 hashes. `MANIFEST.sha256` covers the packaged files.
The inherited sources use the included MIT No Attribution license. Their
arithmetic basis, native logical encodings, whole numerical domain, and
identity bi-interpretation with iPRA remain inherited results.
