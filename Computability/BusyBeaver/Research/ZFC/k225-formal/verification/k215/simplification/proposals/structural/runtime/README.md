# Decoder proof factoring and measured runtime simplification

## Exact formally certified baseline alignment

K215_Formal is the current candidate table SHA9683d6ed… and source17af2071…. A fresh full census and decoder-product check completed on that exact table:281 templates,234 product states,468 edges,97 leaf interfaces;6,176 guards,2,442,801 symbolic steps,2,442,506 exact states,15,675 normalizing endpoint checks. These happen to equal the older K215-variant counts, but are independently rerun and stored separately.

Run `python check_formal_alignment.py`: it parses the included literal KDense215 rows and labels and checks all430 transitions against K215_Formal under301→102,302→120,halt254→230, identity elsewhere. The existing KDense215.commutes theorem binds those literal dense rows to tm215. An independent direct KTable215 parse reached the same exact binding; its receipt is also included. Thus the new current-baseline decoder result is aligned with the actual formal machine, not just its name. No new formal compiler invocation is claimed.

This packet contains owned Python checkers and pinned inert input tables/sources. No imported downloaded code, external packages, or proof compiler are needed. These checks are mathematical/executable evidence, not newly kernel-compiled Lean/Rocq theorems.

Run `python check_decoder.py` from this directory. It verifies all four complete decoder certificates in under a second. The exact context signature is (source DAG node ID, physical state, last up-to-two preceding bits). Source meaning is never inferred from physical state alone.

Results:
- K215: 281 local templates; 234 reachable product states; 468 checked product edges; 97 exposed leaf contexts.
- ST215: 281 templates; 235 states; 470 edges; 95 leaf contexts.
- GC+ZC215: 282 templates; 236 states; 472 edges; 95 leaf contexts.

## Why the internal-decoder argument is universally framed
Each template starts on the last cell of an explicit binary word of length one, two, or three. Every transition must read a cell inside that word. The checker rejects before reading either opaque exterior. It checks that the entire word is restored, the head ends immediately to its right, and the physical state equals the certified exit. Consequently arbitrary exterior tapes remain untouched, by induction on the literal finite transition trace. This is not a claim inferred from a finite selection of register values.

The product checker independently rebuilds the literal source DAG from the complete site list. Every internal product state has both source branches, and each transition agrees with the source child. The source DAG index strictly decreases on internal edges. History is updated by taking the final two bits. At the root, history is the single left marker bit1; no template may require a nonexistent second history bit. This handles the initial blank exterior without assuming an arbitrary second predecessor. Later histories include exactly the preceding code/marker bits. Shared physical-state aliases are harmless because the source node is part of the product state.

Induction on the source DAG proves: for any valid code path, the decoder reaches the last code bit in the appropriate exposed leaf context, preserves the complete code and all other tape cells, and has exact head alignment. The trailing zero pad, register header, arbitrary gap, primary registers and spare list are exterior throughout these internal macros, so they remain untouched. The source depth is checked at most48, below the64-cell header bound.

This factors 155,554 / 141,307 / 155,560 repeated internal-edge uses in the expanded K/ST/GC+ZC source paths. Those are NOT the numbers of complete primitive guards. This certificate does NOT prove the final leaf action, pointer carry/strip return, register engine, source semantics, or overall consistency calibration. The 97/95/95 leaf contexts are interfaces for a further theorem, not already-dischargeable whole-runtime obligations. No globally minimal history claim is made; two bits are a proved sufficient local window.

## Runtime census and modest endpoint-check optimization
The owned analyzer transcribes the inspected Lean KRuntimeCore symbolic step rules, including the existing BoxLemmas oracle. It assumes the corresponding box theorems; it is not a replacement for them. It uses exact branch-aware symbolic states, serialized and losslessly compressed for equality counting. The step/target counts are:
- K215: 6,176 guards; 2,442,801 steps; 2,442,506 distinct exact states; 15,675 normalizing endpoint checks.
- ST215: 6,151 guards; 2,298,318 steps; 2,298,049 distinct states; 15,612 normalizing endpoint checks.
- GC+ZC215: 6,177 guards; 2,442,871 steps; 2,442,513 distinct states; 15,676 normalizing endpoint checks.
All guards reached their exact symbolic endpoint. This includes nontrivial stuttering: intermediate dispatcher states are not rejected.

Thus exact full-state memoization saves only295/269/358 step evaluations, about0.012%–0.015%. Every complete event trace is distinct. Sharing event strings alone is not a sound context theorem and should not be presented as such.

A proposed execCount replaces fuel4000 target-search by an untrusted exact step count, then checks the endpoint once. Its soundness follows by induction using existing sstep_sound and composing Reach/Reach1, retaining the positive-progress bit. The proposed statement is in ExecCount.lean.proposal, explicitly uncompiled. Existing q/head short-circuiting already avoids most normalization work; reducing target tests from millions to guard count does NOT imply a comparable execution speedup. Counted execution is a small, low-risk simplification; the framed decoder product is the more substantial structural opportunity.

To reproduce the census, run e.g. `python analyze_symbolic.py K215 inputs/K215.tm inputs/K215.sites.json`. Repeat for ST215 and GC_ZC215. This takes about1–2minutes per table and appreciable memory because it counts exact symbolic states, not probabilistic hashes. The provided JSON summaries record the prior run and pinned input hashes.

## Exact remaining leaf interface
For each exposed tuple (primitive, argument, physical state, last up-to-two predecessor bits, final code bit), the desired theorem takes an arbitrary code word P·b in the prefix language accepted by the certified source/product. Its precondition includes the unchanged full frame, head at offset|P|, exact physical state, predecessor-history assertion, header-gap constraint, arbitrary register values, nonempty arbitrary spare list, and the appropriate zero/nonzero guard when CD branches. Its postcondition is a positive Reach to the full root-dispatch encoding of the source successor with the exact register and spare-list effect, allowing intermediate dispatcher states. CH instead reaches the designated halting state. The source prefix language must not be discarded: two predecessor bits are proved sufficient for INTERNAL decoder templates only, not for arbitrary leaf/return code.

A further pointer theorem can factor carry and strip operations by induction over prefix bit lists, retaining the number of requested zero/one ancestors and the overflow flag. Exact source checks show all CI/positive-CD increments are nonoverflowing and all CC paths have enough1 ancestors. Break/zero-CD returns still overflow at some sites: K has11011 CB1 and1111110 CD6; ST has111110 CD6; GC+ZC has01111 CB1,11011 CB1 and111110 CD6. Marker movement cannot be dropped. These input sources do NOT have every nonhalt leaf beneath root0. LEAF_SIDE_CONDITIONS.json records the literal checks.

Naming caveat: K215 here means the included table366ae5fe…/source17af2071…, inherited from the earlier candidate packet. It is not asserted byte-identical to every later formally certified object named tm215. The formal files inspected supplied the generic runtime definitions; the concrete census inputs are always explicitly hash-pinned.

The small rejection test also confirms that changed exits, wrong source children, a missing branch, and a bad input pin are all rejected.
