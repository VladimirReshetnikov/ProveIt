# Waterfall: what deadline sharing saves, and what still needs a history compiler

This bounded scout finds a genuine source-level compression and a concrete obstruction. The 46-clock scheduler has a 15-candidate minimum representation using 14 signed relative registers and finite state. At canonical cuts, however, it reduces to the same two half-tape integers and 15-state binary transition table already used by the repository's direct U15 compiler. No fixed-arity unbounded Diophantine certificate or improvement to the 87-operation polynomial follows.

More decisively, [the endpoint counterexample](waterfall_endpoint_alias.md) gives a pinned, integer-only counterexample to replacing history with nonnegative firing counts, the full canonical halt endpoint, and the exact time invariant on this very matrix. An extra count vector has `Mv=194·1`, 62 firings and ten controls. Added to the genuine `(L,R)=(6,0)` halt, it passes all those conditions at the false timestamp622 instead of428. The detailed packet states the precise rejected bundle; the report's full quadratic is unaffected.

## Sources and scope

Read the WIP `waterfall_intake_triage_24a743255.md`, the extracted article's semantics/canonical input/macrostep/quadratic/common-column/endpoint sections and complete matrix appendix, its literal matrix/TM source, and frontend/matrix reconstruction code. Extraction used here is `/tmp/waterfall_intake_triage/waterfall-diophantine`. Archive SHA-256 is `b5d3ee90f9631695afc3c6f34f765b617eb9c631c65ab32705cf3d0e8811a9fc`; matrix SHA-256 is `52cfed3f6cba671ed7b166c126288d555ed687b74622ae5a9aaa5bee1345e46a`. The endpoint packet pins the frontend and article too.

The primary [creator's transition file](https://raw.githubusercontent.com/Iijil1/MTGPrograms/main/Examples/UniversalTM15x2.tm.txt) was checked online against the retained first line. [Neary–Woods, *Four Small Universal Turing Machines*](https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf), Table16 on PDF page17, agrees with the archive's table. Its halt discussion on PDF page19 contains the already documented `c`/`b` prose inconsistency; the missing table entry is `(u10,b)`. This scout relies on the published universality construction, not on a newly proved universal machine. The original publisher metadata differ from the deposited PDF header; see the archive's `SOURCE-PROVENANCE.md`.

Repository comparisons below refer to files under `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`. I inspected the cited interfaces and proofs; this was not another full replay/audit of all those packets. The root agent owns the independent full Waterfall report review.

## 1. Exact control/deadline quotient

Write the thirty control deadlines as

    d_Trans(u,t) = c + [u≠q] + [t≠b].                 (1)

For each side D the two division clocks simultaneously have

    d_DDiv(t) = g_D + [t≠b].                          (2)

At every canonical input these formulas hold. They are preserved by every possible legal next event:

- A noncontrol, nondivision trigger shifts every control deadline equally and shifts both division clocks on each side equally. It leaves q,b unchanged.
- If `DDiv_s` is the unique minimum, necessarily s=b: its other same-side division clock would otherwise be smaller by1. Its trigger changes b to1−b, increases c and both division minima by2, and preserves (1)–(2).
- If a control clock is the unique minimum, it must be `Trans(q,b)`. If that is halt, no update occurs. Otherwise its instruction has destination q'; the compact formula `10−[u=q']+[u=q]+[t=b]−[t=0]` changes (1) to the same pattern with q=q', b=0, c'=c+10. The selected-side division minimum increases1 and the opposite-side minimum10, exactly as the two control-trigger division rows require.

The first bullet follows literally from the six auxiliary row families in article lines489–494; the control formula is at lines501–515. This is induction from source constants, without invoking a macrostep or an asymptotic approximation.

Thus compare only twelve singleton auxiliary clocks, two division minima and one control minimum: **15 candidates**. For a division/control minimum its label is recovered from q,b. Pairwise ties between the retained minima remain undefined, exactly as in the full scheduler. Subtract c from the fourteen auxiliary minima. A control event occurs iff all fourteen signed relative coordinates are strictly positive; an auxiliary event i occurs iff its coordinate is strictly negative and smaller than the other thirteen. The source-dependent update is

    x'_i = x_i + (increment of auxiliary minimum i) − (increment of c).

The q,b changes above are finite control, not uncharged arithmetic predicates. Retaining c as a fifteenth integer recovers absolute timestamps; discarding it preserves event order. Negative relative values and negative increments are essential, so this is not a reduction to the report's independent positive arithmetic-progression streams.

Exact rational rank computations on the retained matrix gave `rank(M)=28` and rank27 after quotienting by a common destination coordinate. These are diagnostic linear-algebra facts, not lower bounds on polynomial circuit size or reachable-state dimension. The nonlinear finite-state invariants (1)–(2) give the stronger reachable representation above.

[the scout checker](waterfall_unbounded_scout_checks.py) and [receipt](waterfall_unbounded_scout_checks.json) checks the constant-row identities for all449 allowed source/control-symbol forms and reconstructs15,266 control/division entries. The portable standard-library helper exposes `verify(source_root)`, pins the matrix/TM/frontend/article before reading, imports no supplied module, and writes nothing through that API. It is a scout checker, not a maintained computation compiler. The proof that a wrong-symbol division clock cannot be selected is the strict one-unit gap in (2).

## 2. Shared columns do not remove ordered dynamics

For a common-column stream model, every source column has form `b_i·1+d_i e_i`. The universal source already fails this for `LeftTape`: its off-diagonal increments include9 at `LeftMult/LeftDiv0/LeftDiv1` and0 elsewhere. Removing a common shift cannot make those entries equal. Such a column changes several competitors' relative order.

More generally the endpoint alias packet proves failure even after requiring complete canonical start and halt configurations and the exact potential identity. Every linear consequence of those equations inherits the alias. An arbitrary finite existential affine/congruence description over natural counts would define a Presburger, hence decidable, input set; it cannot characterize this c.e.-complete halting set on raw `(L,R)`. This obstruction is scoped to affine/congruence schemes: nonlinear arithmetic, digitwise selectors and different encodings remain possible.

The 14-register scheduler is therefore a useful exact interpreter representation, but offers no evident resource advantage over the two-tape macrostep description. Each macrostep already removes all internal scheduler repetitions. Re-encoding the 14-register event history would restore the event-horizon overhead that the supplied macrostep theorem eliminated.

## 3. A concrete constant-field packed macrostep interface

Here is a precise candidate interface worth testing against existing native field-selection kernels. It is conditional until all digitwise typing/selection and shared-length powers are paid.

For a source step j, let d_j=1 for a left move, w_j be its written bit, and r_j the popped bit. Keep natural tapes L_j,R_j. Eliminating the pop quotient gives exactly

    2L_(j+1) = 4L_j−3d_j L_j+2w_j−2d_j w_j−d_j r_j,
    2R_(j+1) = R_j+3d_j R_j+2d_j w_j−r_j+d_j r_j.   (3)

For d=1 these are `L_j=2L_(j+1)+r_j`, `R_(j+1)=2R_j+w_j`; for d=0 they are the opposite move. Thus no quotient witness is necessary once the bits, source instruction and natural endpoint tapes are correctly typed.

Choose a natural field bound K with every source/terminal tape below K and a base B, for example B≥32K+64. For an existential duration k, set P=B^k and pack fields over j<k:

    H=Σ L_j B^j, G=Σ R_j B^j, W=Σ w_j B^j, U=Σ r_j B^j,
    ZL=Σ d_j L_j B^j, ZR=Σ d_j R_j B^j,
    ZW=Σ d_j w_j B^j, ZU=Σ d_j r_j B^j.

Let Q,N pack current/next states and S pack current symbols. Initial q=s=0 and terminal q=9,s=1 give four scalar equations:

    2(H−L0+P Lf) = B(4H−3ZL+2W−2ZW−ZU),
    2(G−R0+P Rf) = B(G+3ZR+2ZW−U+ZU),
    B N = Q+9P,
    B U = S+P.                                      (4)

Every real history implies these by telescoping. Conversely, if every lane is bounded and all selections/table fields are typed, base-digit induction recovers (3) and the state/head links: each local integer residual has magnitude less than B. The large stated base safely bounds even the uncombined coefficient sums. Final tapes may be zero; use natural coordinates or pay positive shifts consistently.

A literal evaluation of (4), with its packed fields and endpoints supplied and comparisons free, costs **27=14M+13A**, using `T=2ZW+ZU` in both tape equations. The tape pair costs22=11M+11A; the state and head equations add3+2 operations. This is only the conditional interface, with four comparisons. It omits all of the following, so it is not a Diophantine certificate operation bound:

1. A proved power/repunit construction for the *same* variable k in the geometry and every stream; natural digit bounds and no extra high fields.
2. Four digitwise selection fields ZL,ZR,ZW,ZU; in particular ordinary integer multiplication of packed d and H is convolution and does not compute ZL.
3. The fixed 29-rule source lookup linking current state/symbol to next state/write/direction, excluding `(J,1)` before the terminal boundary.
4. The ordinary-input recoder and program frame, rather than a free arbitrary raw tape oracle.
5. Every domain shift, equality finalizer and complete polynomial degree/operation ledger.

Here is the literal schedule behind the conditional count. Each numbered
assignment is one binary arithmetic operation; the four equalities following
it are the comparison interface, and their conversion to a polynomial is
unpaid. Constants and copies are free.

```text
 1 t0 = 2 * ZW          2 T = t0 + ZU
 3 a0 = P * Lf         4 a1 = H - L0
 5 a2 = a1 + a0        6 a3 = 2 * a2
 7 a4 = 4 * H          8 a5 = 3 * ZL
 9 a6 = 2 * W         10 a7 = a4 - a5
11 a8 = a7 + a6       12 a9 = a8 - T
13 a10 = B * a9
14 b0 = P * Rf        15 b1 = G - R0
16 b2 = b1 + b0       17 b3 = 2 * b2
18 b4 = 3 * ZR        19 b5 = G + b4
20 b6 = b5 + T        21 b7 = b6 - U
22 b8 = B * b7
23 c0 = B * N         24 c1 = 9 * P
25 c2 = Q + c1        26 d0 = B * U
27 d1 = S + P

a3 = a10; b3 = b8; c0 = c2; d0 = d1.
```

The multiplication positions are 1,3,6,7,8,9,13,14,17,18,22,23,24,26:
14 multiplications and 13 additions/subtractions. Negative intermediate
values are ordinary circuit values, not asserted natural witnesses.

The local check covers1,460 actual macrosteps and64 packed prefixes. It checks (3), all four general-endpoint forms of (4), and the event-count identity below. It neither types arbitrary claimed fields nor supplies a universal certificate.

An additional exact simplification is

    c_j=6+L_j+R_j+L_(j+1)+R_(j+1)−w_j,
    C=6k+(L0+R0)+(Lf+Rf)+2Σ_(0<j<k)(L_j+R_j)−Σ_j w_j. (5)

This follows from `X=2Q+r,Y` and the macrostep count `6+3Q+r+3Y`; r cancels. It can remove redundant local count expressions in a future aggregate. It does **not** make the unweighted sums of packed digits free: evaluation modulo B−1 identifies them only modulo B−1 unless an additional paid sum bound or exact digit-sum certificate is present. Timing remains `tau=1+2C+7k`.

## 4. Comparison with already paid interfaces

- `neary_woods_explicit_universal_tm.md`, especially §§1–3, uses this very29-rule U15 table. Its effective recognizer/clockwise/bi-tag input conversion produces two equal32-symbol bit blocks. `gpcp_history_computed_fields744.md` is a completed successor for the same explicit machine, with ordinary input and program frame paid:744=349M+395A, eight comparisons,122 positive witnesses. This is a whole polynomial, unlike (4). A Waterfall wrapper around it supplies a substrate interpretation, not a cheaper polynomial.
- Direct half-tape packing could use those32-bit blocks without the further tile-alphabet encoding used by GPCP. Given an already paid recoder `q=2^n`, `Qin=q^32`, `z=Σ bit_j(x)2^(32j)`, a block repunit satisfies `(2^32−1)J+1=Qin`. Fixed low-first block values c0,c1 form `D=c0J+(c1−c0)z`; a fixed right-tape frame has form `R0=rho+kappa(D+sigma Qin)`, and the left program tape is fixed for each represented language. These displayed expressions cost9 operations beyond the supplied recoder/Qin (two for the repunit comparison, three for D, four for the frame); if Qin is not supplied by that recoder, five squarings compute q^32. Block orientation and the represented recognizer's bit convention must be fixed together. This is an explicit loader candidate, not a proved substituted production compiler. The archive's four raw-loader operations do not cover it.
- `native_binary_pair_fifo52.md` proves an inexpensive synchronized FIFO transport with ordinary input, but its unrestricted absorbing affine controller has a decidability obstruction. It is FIFO, whereas (3) is a pair of stacks with variable direction; no direct zero-cost substitution exists.
- `two_stack_factored_selector_step.md` already distinguishes a complete scalar one-step certificate from the missing unbounded history compiler. `two_stack_polycyclic_history_obstruction.md` gives good/bad words with the same inverse-group products, heights, multiplicities and endpoints, showing why an affine product alone forgets pop legality. The relative-deadline endpoint alias is the analogous new obstruction for this literal Waterfall matrix.
- `group_four_register_history.md` isolates four packed state histories and eight selected-source fields, with a conditional43-operation interface and explicitly unpaid synchronization/control. Equations(4) need only two tape histories and four selected fields but require the nontrivial U15 finite table and shared geometry. This is the most useful component comparison; it suggests a bounded implementation experiment, not a numerical universal bound.
- `native_single_word46.md` supplies a45-operation positive-word component but no synchronized controller/ordinary-input history theorem by itself. Standalone component counts cannot be added while silently sharing powers or dropping incompatible lane/domain obligations.

## Recommended next step

Publish the literal endpoint alias as a regression for any new count-based scheduler proposal. Then, if pursuing this substrate further, implement only the conditional four-equation schedule(4) against the real U15 table and existing packed selector APIs, with a full charged interface inventory. Compare its completed selector/recoder cost to the direct GPCP and two-stack routes before attempting a 14-register event compiler. The exact scheduler quotient is mathematically useful, but the clearest potential arithmetic benefit is keeping raw binary tape fields through the *direct* macrostep recurrence, not retaining Waterfall's auxiliary clocks.

## Portable scout replay

The helper accepts an already extracted `waterfall-diophantine` directory:

```sh
python waterfall_unbounded_scout_checks.py --root /path/to/waterfall-diophantine --expect waterfall_unbounded_scout_checks.json
```

Use `--output FILE` to write a receipt; otherwise the result is printed. The integer-only portability replay passed with449 finite control forms,15,266 reconstructed entries,1,460 macrosteps and64 packed prefixes, matching the original scout counts. The deterministic receipt additionally records the four source hashes. This helper does not recompute the exploratory CAS ranks or certify the conditional operation ledger. No new mathematical test families were added during portability work.

Helper SHA-256: `70e28478e9e3df365de1073e70a29fcf97d7f5b7136d97cdd309c302e628cdf1`. Receipt SHA-256: `6e89fcdbae3e97ceaba32606784da2aadb156264f410d9888e512e7a875c6093`.
