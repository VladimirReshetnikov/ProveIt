# Independent review of the paired positive7 action factorization

The revised paired-action proof passes independent challenge. It computes the same six increment polynomials on the same52 raw selected-source ports with30M+168A, replacing174M+168A and saving exactly144 multiplications. Its arithmetic identities hold on arbitrary integer assignments to the independent positive/negative slot inputs. Interpreting those increments as an actual selected positive-matrix action still uses the unchanged native one-hot certificate and the accepted sparse-wrapper proof.

This review reads the full author proof, the full paid sparse-action and selected-action structural predecessors, and the full new root sparse-compiler primary proof. It checks the decoder/shear/conjugacy algebra and all instruction counts by hand. It does not evaluate a saved coefficient table, source array or helper, or infer correctness from sample values. Literal local-source metadata is distinguished below from the all-integer proof.

## 1. Exact representation and independent inverse slots

For G(v)=[[v1,-v2],[-v2,v3]], the relation G(S(P)v)=P G(v) P^T proves S(PQ)=S(P)S(Q). In particular

    S(U)(x,y,z)=(x-2y+z,y-z,z),
    S(U^-1)(x,y,z)=(x+2y+z,y+z,z),
    S(V_t)(x,y,z)=(x,y-tx,z-2ty+t^2x).

The b matrices are U V_12 U^-1 in the first block and V_12 in the second. For t=4 or8, the z matrices are U(V_t U V_-t)U^-1 and V_t U V_-t. Their inverses replace V_12 by V_-12 or U by U^-1 inside the same fixed conjugations. These reproduce the exact predecessor matrices, rather than changing the positive alphabet or expanding a macro into multiple lifted letters.

For every invertible C, the identity

    (S(C P C^-1)-I)v=S(C)(S(P)-I)S(C^-1)v

holds for arbitrary v. It applies separately to the independent v+ and v- of an inverse pair; no cancellation between their inputs or selector disjointness is assumed. This is the essential reason factoring the signed arithmetic remains valid even away from native zeros.

The decoder is exactly

    Q^-1 D Z=(Z1-Z4, Z2+Z4-2Z7, Z3+Z4-2Z7,
               Z4-Z7, Z5+Z4-2Z7, Z6+2Z4-4Z7).

The author's u=Z4-Z7 and h=u-Z7 therefore recover the required coordinates. The a decoder never consumes omitted Z1. The b decoder never consumes omitted Z6. Both z decoders use all seven coordinates. Thus the factorizations respect precisely the existing52-port interface; no omitted selected product reappears through a conjugation or common offset.

## 2. The three pair patterns

For an upper inverse pair, write the necessary coordinates as (l+,m+) and (l-,m-). Adding the two independent differences gives

    (2(l_minus-l_plus)+m_plus+m_minus, m_minus-m_plus, 0).

The five charged additions in author equation(7) compute exactly these two nonzero outputs. The a pair pays two7-addition decoders and two5-addition block combinations, totaling24A and no multiplication. Its structural zero outputs are coordinates3 and6.

For a lower inverse pair of amount12, the combined output is

    (0,12(x_minus-x_plus),144(x_plus+x_minus)+24(y_minus-y_plus)).

This needs3M+4A per block. The b input decoders cost9A per sign, including the first-block S(U^-1) coordinates x=v1+2v2+v3 and y=v2+v3. Thus its pre-final-chart cost is6M+26A. Applying S(U) to (0,A,T) separately would cost3A; that valid private exit is omitted in the final shared schedule.

For each z pair, S(V_-t) has the needed coordinates L=tx+y and M=t^2x+2ty+z. The schedule tx, L, L+y, t(L+y), and that last value+z costs2M+3A. With both decoded blocks and signs, this pays8M+34A. Two upper-pair combinations add10A. For each resulting (A,D,0), S(V_t) gives (A,D-tA,t^2A-2tD); the five displayed instructions pay2M+3A. Both blocks therefore bring the pre-final-chart cost to12M+50A. The independently completed first-block S(U) exit would add4A and is omitted in the shared schedule.

All products by12,144,24,t, or other fixed coefficients in these formulas are charged. Doublings are charged additions. There is no division, root extraction, exceptional case or sign-dependent instruction.

## 3. Shared chart and exact paid totals

The four private bodies, stopping before the b/z first-block final charts, cost:

| Pair | M | A |
|---|---:|---:|
| a |0|24|
| b |6|26|
| z1 |12|50|
| z2 |12|50|
| Total |30|150|

The a first-block increment is already in the final basis and stays outside the shared chart. The remaining first-block increments are b=(0,A_b,T_b), z1=(A1,B1,C1), z2=(A2,B2,C2). Summing them costs five additions: one for their first coordinate, two each for the second and third. Applying S(U) to this sum costs four additions. Adding the two nonzero a coordinates costs two more. This is11A for the complete first-block sum.

The last three coordinates have respectively3,4,3 structural terms, so their sums cost2+3+2=7A. All six outputs are now complete. Total aggregation and shared chart cost18A, giving30M+168A. No private chart output that was removed has an additional external consumer at this six-output cut.

Appending the existing uniform relator terms pays24rM+24rA, because each last-block accumulator is already nonempty. Keeping the unchanged positive-output postprocessor gives(40+24r)M+(189+24r)A; its recurrence-fused variant gives(42+24r)M+(189+24r)A. Replacing24r by the separately materialized nonzero pattern count N_R gives the corresponding pruned local schedules. These are local cuts, not complete newly emitted wrappers.

**Review remark 1 (the prior136 saving was valid).** The preliminary author draft completed every pair privately, then paid15 additions to sum its six coordinates. Its30M+176A total and136-operation saving were correct. Omitting the private b/z charts and sharing their final S(U) application reduces the total by eight additions. The revised144 saving does not invalidate that earlier schedule; the author retains it explicitly.

## 4. What can transfer to the complete sparse wrapper

The six final outputs equal the former sum of all48 paired coefficient rows as linear polynomials in the52 selected inputs. This follows from the actual matrix representations and conjugation identities above, not from a finite test. The relator accumulators and positive-lift postprocessor are unchanged. A literal source substitution at exactly these six exits therefore preserves every downstream recurrence residual and the full sum-of-squares polynomial on all supplied integer assignments.

That potential replacement is stronger than the zero-only common-column rewrite used in the earlier dense compiler. Here the local boundary polynomials themselves are equal. It still requires an actual whole-source substitution and consumer audit; this review does not claim that a future wrapper was already emitted or checked.

The native packs,52+8r retained selections,62+10r lanes,96+10r positive witnesses, positive input loader and global S+Ztot+g=P bound remain unchanged. In particular no selected-source unhat, signed coefficient product, selector guard or history proof is removed for free. Once the exact six-exit substitution is authenticated, the existing positive ordinary-input projection applies without a new positivity argument. The signed private intermediates are computed registers, not positive witnesses or native relation parameters.

**Review remark 2 (arithmetic conjugation is not a new lifted word).** The factorization of a fixed signed macro map does not authorize replacement by several positive lifted letters. The baseline has D L(I)=8D, whereas D L(I)^2=64D. Such a word expansion would change the operational action and require separate word-language/controller arguments. No such expansion occurs here.

The universal presentation and numerical relator count remain unmaterialized. The formal local saving is neither a new numerical universal bound nor an optimized-action lower bound. No degree claim or scientific execution is part of this review.

## 5. Frozen bindings and static evidence

This review binds the final author trio:

| Artifact | SHA256 |
|---|---|
| positive7_inverse_pair_action_pascal.md | 3129c00815a83267220dc45fffccf7fa3b05e2523706461221df288fda52a3a2 |
| positive7_inverse_pair_action_pascal.py | 9e079cbef18bc2895113cb42149343fda79dcb6fab2182456f3e1fca325b2dbf |
| positive7_inverse_pair_action_pascal.json | b830a0644ae0b5ba8b04273a3ac445437af0af2c0b522c1caf3078203f7eab02 |

The full final322-line proof,271-line emitter and all198 local row records were read inertly. The final proof added evidence/provenance only after the algebraic challenge; the final receipt retains the original198 rows unchanged. Their compact-JSON source digest is cbbbf4e41204dce42aeb3b6ec379bba34aea5cb162cb42269e5a938077d766d8. The live six-exit order is out_a,out_b,joint_C0,out_d,out_e,out_f; coordinate c is a free alias, not an omitted arithmetic operation.

A fresh independent metadata check authenticates the file/note/emitter bindings, all52 declared raw ports, operation labels, unique definitions, topological closure, backward liveness from the six outputs and the five stage censuses. These stages have respectively24,32,62,62,18 rows, with the multiplication/addition counts in Section3. Every emitted row and declared raw port reaches an output. The hand comparison of the complete literal rows to the displayed schedules supplies their semantic binding; the metadata check does not compute register values or polynomial coefficients.

The author's evidence is one original metadata-only emission, with no optimized or later replay. This reviewer did not run or import that emitter or any predecessor. Only fresh byte and graph-structure processing ran for the review; no arithmetic source or coefficient array was evaluated, no degree propagated, and no repository, Git or frozen artifact changed. The companion JSON records exact dependency bytes and read scope. No future full-wrapper source audit is claimed here.
