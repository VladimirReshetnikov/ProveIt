# Fuse the matrix cleanup cubics into the state evaluation

The four complete sources now cost **1,415 / 1,412 / 1,412 / 1,409 operations**,
saving **two multiplications** in each chart. The complete polynomials and all
supplied coordinates are identical to the corresponding frozen
[selector/scaled compositions](matrix193_selector_scaled_composition.md).
The coefficient component falls from552 to **550 = 302M + 248A** rows.
The witness counts remain141/140/140/139 and the exact degrees remain
35,587/53,345/53,347/71,105.

The change evaluates the X state term and its cleanup cubic together by
Horner's rule. All arithmetic is paid in the [complete emitted sources](matrix193_cleanup_tail_fusion.json).
The separate universal84 bound, ordinary-input compiler, eight fixed context
coefficients, controller, native extension and positive domains are unchanged.

## 1. Concrete joint evaluation

Use baseline register names; the helper verifies their exact mappings into
all three controller charts. Put Q=r108. The existing source has

    cp302 = cp283 + Q^4*cp272 + cp297,
    cp304 = cp284 + Q^4*cp274 + cp300.

The first summand is the already paid copy contribution and the second is
the already paid state polynomial shifted by Q^4. Expanding the actual
cleanup producers gives

    cp297 = -9305414129 Q^3 -1503457720 Q^2
              +45977311 Q +7428465,
    cp300 =  5192707423 Q^3 +838975671 Q^2
              -391960351 Q -63328274.

For example the first cubic is the old fixed row/matrix product

    (22913161 Q+3702035)*(-3869 Q^2-169)
      +(-195915076 Q-31653619)*(-405 Q^2-20).

These coefficients are exact fixed integers derived from the literal parent
numerals. They are not supplied witnesses or a new program-dependent lookup.
Every use of them in the evaluated circuit is a paid addition.

With S0=cp272 and S1=cp274, evaluate instead

    h0 = (((S0*Q-9305414129)*Q-1503457720)*Q+45977311)*Q+7428465,
    h1 = (((S1*Q+5192707423)*Q+838975671)*Q-391960351)*Q-63328274,
    cp302 = h0+cp283,
    cp304 = h1+cp284.

Each column costs4M+5A=9 operations. The old cleanup, state-shift and two
joins together cost5M+5A=10 per column. Thus the saving is exactly1M per
column; no addition or power is free. Q itself and all retained powers
remain paid. The final fixed conjugation and the four coefficient-output
registers retain their old values.

This differs from replacing one output by an existing paid donor: it
introduces a jointly evaluated state/cleanup expression. The analogous Y
cleanup has degree11 and follows a Q^12 shift; the direct corresponding
Horner rewrite is cost-neutral and is not included.

## 2. Full source, private closure and cost

The [fresh standard-library helper](matrix193_cleanup_tail_fusion.py) reads
all predecessors as inert data. It authenticates the full immediate parent
trio and the controller-map receipt. No predecessor code is imported or
executed. A recursive comparison of the four coefficient roots reconstructs
the complete552-row component mapping in each chart and checks it against
the authenticated controller maps, rather than assuming matching array order.

In baseline names the private deleted producers are `cp285` through `cp301`
and `cp303`:18 rows. The two target names `cp302` and `cp304` remain, with
the displayed new definitions. Sixteen new intermediate rows are paid.
Exactly these deletions, additions and two retained-definition changes occur
in each chart. Every old deleted value has consumers only inside the deleted
cone or at one of the two restored targets. The simultaneous full graph is
rescheduled, checked for cycles and sequential operand availability, and
traversed from the actual complete output. Every row and supplied port is live.

| Chart | M | A | Complete | Witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|
| No positive controller chart |683|732|**1,415**|141|35,587|
| Flow |682|730|**1,412**|140|53,345|
| Population |682|730|**1,412**|140|53,347|
| Both |681|728|**1,409**|139|71,105|

The complete coefficient cone is550=302M+248A in every case. All242 shared
selector rows, all97 grouped-population rows, and all63 native rows remain
literal. The full finalizers are traced from their actual output expressions,
including their interleaved chart rows:50/47/47/44 rows for16/15/15/14 ordinary
residuals. Those rows remain literal, as does every other retained definition
outside the two target edits. There are143 distinct integer literals in each
new source, versus137 in the immediate parent. This is a fixed-numeral recipe
tradeoff, not an uncounted arithmetic operation.

## 3. Exact identities at the actual computed fields

For each of the two target definitions in each chart, a fresh sparse
polynomial interpreter expands its complete old and new ancestor cone at
three cuts: the **actual computed Q**, the **actual state register**, and the
**actual copy register**. Both expansions equal

    copy + state*Q^4 + the displayed cleanup cubic.

This is an identity in three formal variables, so dependencies among these
computed fields require no extra premise. It holds before any zero equation,
selector typing, positivity, determinant condition or fixed-program recipe.

The helper then binds the proved local expression to the actual Q/state/copy
values in both full expression DAGs. It verifies the identical computed-Q
expression and compares every retained register and the whole output. The
retained-register counts are1,399/1,396/1,396/1,393; the16 new intermediates in
each array are not claimed to be old registers. The entire parent packet is
checked to remain unchanged in memory.

A separate pure-Q interpreter expands all four full coefficient words in
each chart and compares every coefficient with its saved immediate-parent
certificate:16 words,2,704 coefficient entries. Thus neither the local cubic
formula nor the whole-source proof silently replaces a computed field by an
independent supplied parameter.

For each chart j, the resulting theorem is the full polynomial identity

    F_new,j(x,fixed_context,witnesses)
      = F_parent,j(x,fixed_context,witnesses)

on identical supplied coordinates over every commutative ring. The complete
positive integer zero sets therefore agree via the identity map. The parent's
ordinary-input theorem transfers on its unchanged valid fixed-context recipes.
The older terminal-carry and IDLE transformations retain their previously
stated ordinary-input scope; this packet supplies no stronger inverse for them.

The exact degrees transfer from these complete identities, also after any
valid fixed-context specialization. No dense expansion of the large final
polynomials is asserted. The separately recorded syntactic upper bounds are
36,547/54,785/54,785/73,023; they are not substituted for the inherited exact
degrees.

## 4. Frozen inputs, checks and scope

| Inert dependency | SHA-256 |
|---|---|
| `matrix193_selector_scaled_composition.py` | `b220ba4a91370af19be84ab215dab3cf844dca16d026c08d7c0a8e85c62f6639` |
| `matrix193_selector_scaled_composition.json` | `762692a86d5020ffe89357d875803e927750546dbd946e309a2b48b6df73ce29` |
| `matrix193_selector_scaled_composition.md` | `96e6bc689c02ba789de5bed95b091a7560aba3a6a43a1428c6e0f3038bd61b5a` |
| `matrix193_entry_controller_charts.json` | `d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571` |

The receipt includes all5,648 new rows, source and helper hashes, both local
identities and their actual bindings per chart, exact private deletion lists,
all16 dense coefficient vectors and the complete ledgers. Thirty-two signed
full-source comparisons over two prime fields additionally check every
retained register; half use the saved fixed-context fixture, and half vary
the fixed ports. These are supplementary algebra checks, not accepted histories
or materialized positive native Pell tuples.

The helper rejects duplicate JSON keys and noninteger JSON number encodings.
Explicit guards survive optimized Python, and canonical JSON comparison
preserves number types. Source generation requires a fresh output path.
Fresh normal and optimized exact receipt replays from `/` passed:

```sh
matrix_wip=/absolute/path/to/native-stream-queue
python3 "$matrix_wip/matrix193_cleanup_tail_fusion.py" \
  --root "$matrix_wip" --expect "$matrix_wip/matrix193_cleanup_tail_fusion.json"
python3 -O "$matrix_wip/matrix193_cleanup_tail_fusion.py" \
  --root "$matrix_wip" --expect "$matrix_wip/matrix193_cleanup_tail_fusion.json"
```

New helper SHA-256:
`52113307be60663b792a5ac62a7dc18ca35355d1a534faba4163c9b6d6047089`.
New receipt SHA-256:
`61cbef79077bc3c5527c71f0abbeaac967f3d342f83bb8b9019ccdaa89857fe1`.

Only these four actual matrix arrays are emitted. There is no new diagnostic,
new history-packing architecture, or circuit-minimality claim. No repository
file or frozen predecessor was changed.
