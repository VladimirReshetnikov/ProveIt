# Independent review of selector/scaled-power composition

**PASS.** The four complete sources in
[matrix193_selector_scaled_composition](matrix193_selector_scaled_composition.md)
correctly compose the paid scaled-power reuse with selector-block sharing.
There is no remaining source, arithmetic or scope finding.

| Variant | M | A | Total | Positive witnesses | Inherited exact degree |
|---|---:|---:|---:|---:|---:|
| No controller chart | 685 | 732 | 1,417 | 141 | 35,587 |
| Flow | 684 | 730 | 1,414 | 140 | 53,345 |
| Population | 684 | 730 | 1,414 | 140 | 53,347 |
| Both | 683 | 728 | 1,411 | 139 | 71,105 |

## Frozen scope

| Author file | SHA-256 |
|---|---|
| `matrix193_selector_scaled_composition.py` | `b220ba4a91370af19be84ab215dab3cf844dca16d026c08d7c0a8e85c62f6639` |
| `matrix193_selector_scaled_composition.json` | `762692a86d5020ffe89357d875803e927750546dbd946e309a2b48b6df73ce29` |
| `matrix193_selector_scaled_composition.md` | `96e6bc689c02ba789de5bed95b091a7560aba3a6a43a1428c6e0f3038bd61b5a` |

I read the full author helper and proof, both immediate branch notes,
and the saved source/interface data. The fresh
[review checker](review_matrix193_selector_scaled_composition.py) authenticates
this trio and all nine branch/map dependency pins. Its
[receipt](review_matrix193_selector_scaled_composition.json) records the
independent checks below. Frozen predecessors are read only as data; none
is imported or executed. Only the fresh composition author and fresh
reviewer helpers were replayed.

The immediate selector-sharing JSON pin is
`cfaab226e28465ee1332bd38915ca49e6befe91a2931181d19eaf66603121584`.
The scaled-power JSON pin is
`c81bb0ef774361b1b8b4f1b6084ec90329f9c0e22665d8968ced5517959de2b4`.
The controller-map JSON pin is
`d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571`.
The complete nine-file hashes are retained in the reviewer receipt.

## Independent reconstruction and identity

The checker derives the changed and missing definitions directly by comparing
the complete arrays, before comparing them to the claimed edit. Each variant
has exactly one deleted multiplication and one changed retained definition,
with no new register. In baseline names these are

    old: cp344=Q^162; cp345=−20*cp344,
    new: cp345=cp317*cp400,
    paid operands: cp317=Q^150, cp400=−20*Q^12.

The deleted power's sole old consumer is cp345. Exact integer polynomial
expansion checks the old value, both paid new operands and the new target.
All 627 retained pure-Q values per variant agree. Rescheduling preserves
sequential operand availability and all non-pure-Q execution order.

An independent full expression interpreter normalizes these exact pure-Q
polynomials while binding Q to its actual expression in the supplied ports.
The edit is outside Q's ancestor cone, and both actual Q expressions agree.
Every retained source register, including every final output, then agrees
formally. This establishes the entire polynomial identity on identical
supplied coordinates over any commutative ring; it is not a finite modular
test or a proof that assumes Q is an independent free variable.

The complete coefficient component is literally the same 552-row schedule
as the scaled-power branch, with304M+248A. The complete selector component
is literally the same 242-row schedule as the immediate selector parent,
with121M+121A, including its execution order and two word contracts.
The checker expands all sixteen coefficient words and verifies all2,704
stored integer coefficient entries against both parents.

All63 native and97 group/population definitions are literal retained rows.
Each parent and child finalizer is independently traced backward from its
actual output through the native multiplier, one-plus-SOS and every residual
square and sum. The50/47/47/44 rows and16/15/15/14 residual lists are identical,
with no omitted or duplicated residual and no assumed contiguous suffix.

All5,656 emitted binary rows pass unique-definition, operand-type, topology,
free-port and liveness checks. The witness lists, eight fixed coefficient
ports, ordinary input, illustrative fixed bindings, output registers and137
integer literals remain unchanged. Complete counts are derived from the
arrays, not obtained merely by subtracting advertised branch savings.

## Degrees, domains and validation

Full equality to the immediate selector parent transfers its exact-degree
statement on the identical variables and valid fixed-program specializations.
The independently propagated syntactic degree upper bounds are instead
36,547 /54,785 /54,785 /73,023; they are not substituted for the inherited
exact degrees. No new dense expansion or highest-component proof is claimed.

The same identity preserves full positive integer zero tuples of each
immediate parent. It supplies no stronger common-coordinate inverse across
the earlier terminal-carry or IDLE charts, whose stated equivalence remains
ordinary-input only. The inherited natural ordinary input and fixed-program
recipe are unchanged. No arbitrary coefficient assignment, new accepting
trajectory or universal bound below84 is asserted.

Fresh normal and optimized author replays from `/` passed against the installed
inert dependencies. The independent reviewer likewise passed fresh normal and
optimized exact receipt replays from `/`; its guards remain active under `-O`.
No historical builder or predecessor helper ran.

Reviewer helper SHA-256:
`5a80e157709d2aba4e8711eab68fe997d8dce3c4b13e4fda0f6a5ab82c79e73d`.
Reviewer receipt SHA-256:
`908a323a757128d29be209f0276af20e4a74d7217ec9b1747b90b1e19c37bfc4`.
