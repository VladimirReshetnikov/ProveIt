# PA195 bounded halting and conditional PA consistency endpoint

This directory connects a precise PA195 transition table to an arithmetical
halting sentence. It does **not** prove either direction of the claimed
machine-specific equivalence in iPRA, PRA, or PA. The machine-specific
reductions remain hypotheses in `PA195Endpoint.lean` and
`PA195ForwardGG.lean`.

`generate.py` reads the archive `docs/incoming/pa195_conpa_2026-11-13.zip`
and refuses any other bytes. Its SHA-256 is
`0001250c43a40920027403d748bcca36e4519a5a45e94dec98cafad4f3c8ff9f`;
the member `pa195_conpa/pa195/pa195.tm` has SHA-256
`5c6afd87f7c4f24d9ad8e9e302cc21df14b6f2e3715d03322a75463a431d8455`.
The generator validates that the member describes 390 transitions, one for
each bit and working label 0–194, all targets are 0–195, and all 195 working
labels are reachable in the transition graph from 0. Terminal label 195 has
no transition. Graph reachability and archive parsing are Python checks, not
Lean theorems; the generator is part of the trusted route from the archived
bytes to the two temporary Lean definitions. Those definitions use different
representations but are generated from the same parsed table. Lean checks that
their 390 entries agree. No generated table is tracked here.

`PA195Bounded.lean`, adapted from the corresponding PA196 bridge, defines a
two-stack natural-number configuration, proves its step and bounded halting
test primitive recursive, and proves that the test matches `M6.Zip` halting
for the generated PA195 literal machine on the blank tape. A primitive
recursive function code is chosen using classical choice; the code is not an
explicit serialized numeral. The resulting native iPRA sentence is proved to
have the same truth value as machine halting in the standard natural numbers.
These metatheoretic bindings do not establish a proof inside iPRA.

`PA195StandardSemantics.lean` identifies the native PA consistency sentence
with ordinary PA consistency in the standard model, and identifies the native
halting sentence with the above machine halting. `PA195Endpoint.lean` assembles
the desired iPRA equivalence if the two displayed machine-specific reductions
are supplied. `PA195ForwardGG.lean` derives the forward iPRA reduction from an
explicitly assumed classical PRA reduction; it does not prove that reduction.
`PA195RefutationBridge.lean` binds the mapped PA refutation formula to a
Foundation PA proof-code witness in models whose arithmetic reduct satisfies
IΣ₁. That semantic assumption is stronger than the candidate PRA assumptions;
the witness may be nonstandard, and no relation to the machine's checker is
proved. None of these results establish the missing machine reductions.

To rerun the checks from the repository root, supply matching prebuilt Lean
4.32 project and Foundation object directories, for example in the development
environment:

```sh
TMPDIR=/dev/shm \
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
bash Computability/BusyBeaver/Research/PA/pa195/ipra/check.sh
```

The script regenerates the two table definitions and recompiles the local
modules in a private temporary directory. It checks a few direct source hashes
but assumes its supplied transitive object caches match their sources; it is
not a clean rebuild of those dependencies. It prints theorem axiom dependencies
and rejects `sorryAx` in the checked declarations.
