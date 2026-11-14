# PA194AX11QH: a new 194-state composite candidate

This package constructs **PA194AX11QH**, a concrete binary single-tape Turing machine with 194 working states, 388 transitions, blank two-way tape, head at coordinate zero, start state zero, and separate halt label 194. Its new composition combines four supplied mechanisms at coefficient four: exchanged quantifier-distribution premises (Q), the eleven-entry AX fall-through interface (AX11), no-push modus ponens (N), and a cached-only contradiction test (H).

**Proof status:** the package supplies exact construction, complete source bindings, symbolic command identities, simultaneous local folds, independent literal-tape contracts, and complete blank initialization. It does **not** supply a completed proof in iPRA that this physical machine's nonhalting is equivalent to Con(PA). The pinned repository explicitly leaves that baseline calibration open. Any consistency equivalence must retain its stated arithmetic-calibration premises. No end-to-end Lean or Rocq theorem is claimed.

The machine is graph-distinct from the 82 spanning 194-state classes in the independently audited current corpus, even allowing arbitrary spanning roots, state renaming, tape reflection, symbol complementation, and arbitrary effects on terminal transitions. That novelty check is retained separately in the enclosing report package. It is a new combination of prior mechanisms, not a new axiom calculus and not a state-count reduction.

## Exact artifacts

- `machine/machine.tm`: dense transition table, start 0, halt 194.
- `machine/machine.native.tm`: native labels, start 74, halt 254.
- `machine/labels.json`: dense-to-native bijection, including halt.
- `machine/raw.native.tm`: 201-control parent before seven simultaneous folds.
- `machine/nodes.json`, `grammar.json`, `grammar.tree.json`, `sites.json`, `instructions.json`: complete source description and resolved graph.
- `machine/independent/`: independent complete tape certificates and replay receipt.
- `proof/`: free-term emitter, command, scheduler, full source binding, and 61-line premise-exchange checks.
- `research/emission_order/`: bounded reduction search, exact source, inputs and log.
- `PROVENANCE.json`, `INPUT_HASHES.json`, `licenses/`: attribution and pinned construction inputs.

Dense SHA-256:

```text
19e215df20429fa6a35f0a99ba0dcfcb40893a6e4b9a4ae6e450b0225f110e50
```

Native SHA-256:

```text
424bd5175bbca161e76af485f1eda03f2f169d90afe80563035b60289361bf07
```

Each row is `state read write L_or_R next`. There are no outgoing rows for halt. Native labels do not count states.

## What changes in recurring computation

Let `p` be Cantor pairing, `[a;w]=p(a,w)`, and `I(a,b)=4p(a,b)`. A store is `(t,w,d,h)` (visible theorem, stack, offset, cached theorem). Put `D=d+x`, `H=h+y`.

The new command `AX(c,x,y,z)` consumes four parameters. It pushes the guarded gate and nine other generated theorem entries, followed by the saved visible theorem, then consumes the extra field `z` by falling through the full MP reader:

```text
AX(c,x,y,z):
(t,w,d,h) -> (0,[G,Gamma,L6Q,L5,L4,L3,L2,L1,rho,U(d,h),t;w],z,0).
```

Here a failed gate guard outputs zero, and `L6Q` is the premise-exchanged universal-distribution theorem. Its equivalence to the old head uses the included finite premise-exchange certificate.

For `b=d+x`, MP returns `(b,w,b,0)` if `I(t,b)=h`, and `(0,w,b,0)` otherwise. It does not push the old dummy zero. Shift halts exactly when `h=1`; otherwise it returns `(h,tl(w),d,hd(w))`.

The old AX11 command proof cannot be copied without adjustment. With `A0=AX(0,0,0,0)`, `Push=A0;S^10;MP(0)` remains total. `Pop=A0;S^12` preserves a visible theorem different from one; if that theorem is one, Pop halts. The proof compiler therefore permits early contradiction halting. A final visible contradiction can always be exposed by `Push;S;S`. A lone Shift does not test a visible one when the cache is zero.

The symbolic command checker explicitly covers these cases, including the collapsed Cantor pair `[0;0]=0`. The compiler chooses the fourth AX parameter `z=0`; soundness must cover every `z` because the scheduler enumerates every candidate.

## Fresh observed verification

| Check | Result |
|---|---:|
| Working states | 194 |
| Transition rows | 388 |
| State allocation | 134 fixed + 67 readers - 7 folds |
| Local simultaneous fold cases | 28 |
| Primitive source sites | 3,671 |
| Universal source outcomes | 4,778 |
| Construction symbolic operations | 1,547,747 |
| Independent symbolic operations | 1,130,254 |
| Independent maximum case length | 403 |
| Minimum positive duration constant | 3 |
| Generic list lemmas rederived from rows | 4 |
| Complete blank startup steps | 57,922 |

The independent checker imports neither the construction compiler nor its arithmetic-box oracle. Its contracts cover nine arbitrary natural register values, both decrement branches, an arbitrary nonempty finite list of arbitrary natural spare values, and an arbitrary affine header gap. Its independent startup run checks the whole finite-support tape and its zero exterior. A finite startup run is used to establish an initial frame, never to infer nonhalting.

## Offline reproduction

Use Python 3.10 or newer, standard library only. Keep assertions enabled.

```sh
python3 -B verify.py --receipt fresh_verification.json
```

This rebuilds in a temporary directory, checks exact delivered tables and all source artifacts, runs the construction symbolic engine, independently resolves the source graph twice, checks the emitter and command identities, replays the premise-exchange certificate, and reruns the independent literal-tape engine. Temporary outputs are removed; the optional receipt is retained.

```sh
python3 -B verify.py --quick --receipt fresh_quick_verification.json
```

Quick mode skips only the independent literal-tape engine. It records that omission. These are executable certificates, not a consistency proof checker.

## Reduction search

The new search allows permutation of seven separately emitted theorem heads and binary reassociation, with exact simultaneous fold compatibility near the frontier. In the recorded 240-second run it considered 3,631,115 proposals and accepted 650,390 search moves. The best effective reader count remained 60; with 134 fixed controls that is 194. No sub-194 result was obtained. The search is bounded and heuristic; it proves no state-count lower bound.

A companion 90-second run used the composite H controller to make its different provider transitions available to decoder folds. It considered 1,283,873 proposals and accepted 221,857 moves, again with no sub-194 hit. Both logs and seed files are retained.
