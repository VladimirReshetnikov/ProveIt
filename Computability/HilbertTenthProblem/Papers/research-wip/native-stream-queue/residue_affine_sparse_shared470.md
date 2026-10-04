# Reuse control pairs in the two-program U21 compiler

The complete source in `residue_affine_sparse_shared470.json` has **470 = 175M + 295A operations**, **67 positive witnesses**, two fixed program parameters and ordinary positive input. Its certificate costs **450 = 168M + 282A**. It computes exactly the frozen 476-operation parent's polynomial on identical supplied coordinates and retains the uniform degree bound **at most 5160**.

Five additions disappear by reusing already paid control pairs in prime-selector prefixes; one multiplication disappears by reusing a paid population prefix in the current-control expression. The six rewrites are applied directly to the complete two-program 476 array. The separate 471-operation one-program source supplied the rewrite strategy, but it is not the parent or a claimed positive-coordinate counterpart of this packet.

## 1. Exact parent and fixed interface

The authenticated parent is `residue_affine_sparse_shared476.json`, with parameters `program,radix_program,input`, written E,C,x. The first two are fixed program parameters; the remaining 67 supplied coordinates are positive witnesses. The actual height/radix rows remain literally

    height_85 = input + height_slack;
    radix_86 = radix_program * height_85.

Thus h=x+eta and B=Ch. For the inherited universal U21 recipe, fix E=3^e and a dyadic C satisfying C>=64 and C>E, independently of the varying ordinary positive input x. These are fixed-slice recipe hypotheses, not new unpaid polynomial constraints. The default literal control plan remains the only supported plan in this successor.

The existing 504 proof supplies soundness and fresh positive completeness for this two-program recipe; the 476 proof transfers it by exact polynomial equality. The present identity preserves the entire positive zero tuple in both directions, so it requires no new history reconstruction, changed native coordinates or positive-slack argument. The one-program height E+x+eta and radix64h are not used here.

## 2. Six exact rewrites

Write E_j=edgej_hat−1. These are formal affine expressions; no Boolean or nonnegative-digit premise is used.

The following pairs are already paid and live in the 476 parent:

| Existing register | Exact value |
|---|---|
| `control_codes__target_class_35` | E17+E28 |
| `control_codes__duplicate_state_3` | E30+E31 |
| `control_codes__duplicate_state_2` | E18+E19 |
| `control_codes__duplicate_state_5` | E20+E21 |
| `control_codes__duplicate_state_8` | E24+E25 |

Use them in these five retained target definitions:

    prime_selector_99  = edge_16 + control_codes__target_class_35;
    prime_selector_101 = prime_selector_99 + control_codes__duplicate_state_3;
    prime_selector_105 = prime_selector_103 + control_codes__duplicate_state_2;
    prime_selector_107 = prime_selector_105 + control_codes__duplicate_state_5;
    prime_selector_109 = prime_selector_107 + control_codes__duplicate_state_8.

Each replaces two successive additions of single selectors by one addition to a paid pair. The private old intermediates `prime_selector_98`, `prime_selector_100`, `prime_selector_104`, `prime_selector_106`, `prime_selector_108` have no other consumers and disappear. This saves five additions. The pair producers remain paid and live; their raw-selector dependencies permit the required earlier scheduling.

For the sixth identity let

    G3=prime_selector_93=E2+E3+E13;
    G5=prime_selector_95=E32+E33+E34;
    u21_grouped_J_0=G3+G5.

The old `control_codes__current_positive_19` is G3+2G5. Replace it by

    control_codes__current_positive_19 = u21_grouped_J_0 + prime_selector_95.

The addition is retained; its sole old private scalar product `control_codes__current_multiple_9=2*G5` disappears, saving one multiplication. The population prefix remains paid and live in J. No fixed scalar multiplication is silently free.

All six edits are simultaneous. The helper reschedules dependencies and proves acyclicity and sequential operand availability; it does not assume that separately valid rewrites compose without a cycle. No new register is added. Exactly six old registers are removed, and exactly the six displayed retained definitions change.

## 3. Complete polynomial and positive-zero identity

The new helper builds fresh row lists and checks that both the parent source and its entire packet remain byte-identical in memory. For each changed target it expands the complete old and new ancestor cones in two ways: as an affine polynomial in actual supplied hats, and as an affine polynomial in formal raw selectors. It verifies both equalities and the constant conversion induced by E_j=edgej_hat−1.

Those proved actual-hat expressions are then bound to the actual free ports in a full expression interpreter. Every one of the 470 retained registers has exactly the parent's value, including all downstream native inputs, norm factors, ordinary residuals and final output. Every retained definition outside the six named targets is literal. In particular all 72 native-prefixed rows, six ordinary residual rows and 20 finalizer rows are unchanged.

Consequently, over every commutative ring,

    F470(E,C,x,witnesses)=F476(E,C,x,witnesses).

This equality needs no zero equation, typing theorem, sign premise or fixed-program restriction. It gives equality of full positive integer zero sets on identical supplied coordinates. On the valid fixed recipes in Section1, the parent's ordinary-input representation transfers directly. No relation between the supplied positive coordinates of 470 and 471 is asserted.

## 4. Complete paid ledger

| Stage | M | A | Operations |
|---|---:|---:|---:|
| Parent certificate | 169 | 287 | 456 |
| New certificate | 168 | 282 | 450 |
| Literal finalizer | 7 | 13 | 20 |
| Complete new polynomial | **175** | **295** | **470** |

The certificate retains seven comparisons in the parent's convention: six ordinary residuals and the native/repunit product condition. Counts come from the full emitted source, including pair producers, all fixed-numeral products, input machinery and the finalizer. All 470 rows and all 70 supplied ports are live; the witness list and the two fixed-parameter list are unchanged.

## 5. Fresh degree guard

Full polynomial equality transfers the parent's uniform bound, but the helper also checks it directly on the new source. Twelve literal native definitions authenticate the main-norm identity at the actual fields X,a,c,G,H:

    (X+ac+G)^2 − (a^2+H)c^2
       = X^2+2acX+2GX+2acG+G^2−Hc^2,
    H=4a+3, G=ga*H.

With every supplied port, including E and C, assigned degree one, the bounds for X,a,c,G,H are 312,379,68,380,379. The six surviving term bounds are624,759,692,827,760,515, respectively. Thus the native main factor has degree at most827, rather than the naive gate bound894. This cancellation is an all-value polynomial identity, not a substitution of a norm equation.

Propagating from this guarded cut through all actual rows gives the eight factor bounds

    827,1926,448,66,1032,380,380,3,

summing to5062. The largest ordinary residual has degree at most49, so the literal product finalizer has degree at most5062+98=5160. Propagation without the proved cancellation gives5227. The receipt saves both bounds and the exact six-term coefficient expansion. Specializing E,C to fixed numerals cannot raise the uniform bound. No exact degree is claimed.

## 6. Frozen evidence and scope

The fresh standard-library helper authenticates these inert dependencies; none is imported or executed:

| Dependency | SHA-256 |
|---|---|
| residue_affine_sparse_shared476.py | `52e09d2b3474e37c6116e16b7a1ee59395a337a5ff381b4881ae616ecbaafddf` |
| residue_affine_sparse_shared476.json | `90e6e265ae1eb9a1cd1239255c14da3d3c6e5841f330f7a6220536d182778ba8` |
| residue_affine_sparse_shared476.md | `cbd4d632b813f0ad34a9e5b35894d187ca229c14f1d4cf3af269a518ab57fcd4` |
| residue_affine_sparse_program_radix504.md | `4c3e0545b8f7f025096a30170a1785d33da35b625e3aa8dacb1362a461d0a549` |
| residue_affine_sparse_factored.md | `b169236c449623049759b7ac0877b2202b3aba389ace8e06d31370396abb9ea7` |
| residue_affine_sparse_control_codes.md | `be133b5d93c082c3f3022e4b9990140ff3de71cf7202a7ba281a48e8c77d34da` |
| native_binary_norm_units.py | `1f088e43e60f068f2ca7c78a607f4cc5cd4ec34b7d2d5259c9ce545f74fdfee9` |

The helper adapts the data-only utility structure and six edits from the separate 471 helper as inert text. Its actual input array, interface checks, source identity and degree guard all use 476 directly. The receipt contains every new source row, source and helper digests, all six affine identities, private-consumer lists, native/finalizer boundaries and the fresh degree calculation.

Additional checks compare all retained registers on 32 signed assignments over two finite fields and four signed rational assignments. These corroborate algebra off the zero set; they do not materialize an accepting history or a positive native Pell tuple. Full symbolic identity supplies the positive-zero theorem.

The parser rejects duplicate keys and noninteger JSON numbers; explicit runtime guards remain active under optimized Python. Receipt comparisons are canonical and type-sensitive. The source exposes `--root ABS_WIP` and exactly one of `--output NEW_PATH` or `--expect RECEIPT_PATH`.

Only this default two-program coupled-product source is emitted. There is no new minimum claim, no new semantic compiler construction, and no change to the separate complete universal84 bound. No repository or frozen predecessor was changed.

The writer and fresh normal and optimized exact receipt replays from working directory `/` passed. Both replays used absolute source, root and receipt paths.

New helper SHA-256: `6705f2abfc330427f47aaf8ee3cbad25ca311e86014e0499c994fdf90b97a586`.

New receipt SHA-256: `2f7715aa5449118cfad292595bc7cde374587723a123b3c69a0d180cb51993e4`.
