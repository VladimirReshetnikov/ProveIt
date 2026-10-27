# Actual C222 GEN/MP rule checkpoint

26 October 2026. Read-only proposal after frozen Leaf142/Checks58; no new
Lean source or compilation. Re-read the complete actual Leaf, Block,
Composition, the relevant Step/Run graphs, actual EnumPerm block definitions
and symbolic runs, and historical RuleExecution254 as a guide only.

Propose `ArithmeticCommandRulePerm222` plus Checks, about150–190 main lines
and55–70 checks, importing only Leaf after root accepts it. All numeric
parameters below range over an arbitrary internal IΣ1 model. Let `append`
denote actual `appendValue`, and reuse actual `terminatorWord` from Leaf.
The exact fixed numeric words are:

```
genTail i = dropWord
  (append (Jword i) (nipWord
    (axWord i 0 0 (append (nipsWord 9) terminatorWord))))
genBlockWord i p = append p (genTail i)

mpTail B = nipWord (dropWord (nipWord (mpWord B
  (axWord B 0 0 (append (nipsWord 10) terminatorWord)))))
mpBlockWord B pa pab = append pa (dropWord (append pab (mpTail B)))
```

Every cons uses the already checked shifted actual word encoding. AX has
three payload arguments in API order c,x,y, physically packed y,x; u is the
old counter, not an extra payload. Historical254 RuleExecution's constructor
definitions therefore cannot be imported or reused definitionally.

## GEN: exact state path, then contract

Target `eval_genTail i H S`:

```
evalValue (genTail i) (stateValue H S 0 0)
  = someState (wal i H) S 0 0
```

There is no H≠1 or i>0 premise. DROP changes the state to
`(0,P H S,0,0)`. The actual J(i) lemma changes only the counter to i, even
when i=0 (where J is the empty word, not MP0). NIP tests the old cache0,
loads H, and gives `(0,S,i,H)`. AX(i,0,0) immediately consumes this cache;
it does not test H for falsity. It produces gate(i,H,i)=0 and
`axStackValue i H H i i 0 S`.

The eight entries before the selected universal row are exactly

```
rho1 i H, rho2 i H i, rho3 i H i, rho4 i H i, rho5 i H i,
rho6 i i, growG i H i, rho8 i H i i.
```

Thus the missing finite helper `gen_cleanup` is the existing `select_entry`
at this eight-entry prefix, x=wal(i,H), empty suffix, gate0, last0. It proves
`NIP^9;DROP;NIP;NIP` restores S and both counter/cache zeros. All tested
entries differ from1 by actual axList and wal facts. The fixed list split
and `nipsWord 2 = nipWord(nipWord 0)` suffice; no new arithmetic induction.

Then `gen_contract i (hp : Contract p H)` proves
`Contract (genBlockWord i p) (wal i H)` by the two actual append branches:
child halt remains halt; child positive success invokes the exact suffix.
The Contract quantifiers remain all initial top/S, not merely a clean
zero-stack input or a semantically valid formula.

## MP: both literal false branches and saved-major input

Target `eval_mpTail A B S`:

```
evalValue (mpTail B) (stateValue (wim A B) (P A S) 0 0)
  = if A=1 ∨ B=1 then 0 else someState B S 0 0
```

First NIP tests0 and loads A. DROP makes top A and saves wim(A,B) over S,
retaining cache A. The next NIP halts if A=1; otherwise it loads wim(A,B)
while restoring S. MP(B) succeeds by literal equality and produces
`(B,P 0 S,B,0)`. Cleanup AX(B,0,0) has **old counter B** and produces
gate(B,0,B)=0 plus `axStackValue B 0 0 B B B (P 0 S)`.

The missing finite helper `mp_cleanup` states:

```
evalValue (append (nipsWord 10) terminatorWord)
  (stateValue 0 (axStackValue B 0 0 B B B (P 0 S)) 0 0)
  = if B=1 then 0 else someState B S 0 0.
```

Ten NIPs consume the nine non-false AX entries and load the old top B.
The final DROP retains cache B. Its next NIP therefore tests B and halts
when B=1. Otherwise the final two NIPs consume the two explicit saved zeros,
restoring precisely S. Neither helper may silently replace old u=B by0.

Finally `mp_contract (ha : Contract pa A) (hab : Contract pab (wim A B))`
proves `Contract (mpBlockWord B pa pab) B` with no A/B non-false premise.
After successful minor execution, DROP invokes the major contract at
**top0 and saved stack P A S**. Either child's halt is absorbing. If both
return, the suffix gives halt or the required positive success. False
branches are allowed behavior of Contract, not failed theorem hypotheses.

## Representation boundary and focused checks

These are fixed numerical functions built from actual pair/add/append and
the represented zero-conditional J loader. Child word operands p,pa,pab are
arbitrary internal values. This checkpoint does not assert they arise from a
proof-code compiler and does not identify them with historical254 Circuit
values. Existing pair/append/J graphs make a later fixed Sigma1 circuit
encoding feasible, but no new Circuit datatype/graph or global row function
is needed for these four exact word definitions and contract preservation.
In particular, pointwise `Contract p H` is not silently promoted to a uniform
represented proof-to-word transformation. The unrestricted-rho8 finite circuit
and proof/history induction remain separate.

The Nat-facing definition check can use the already imported `encodeList`,
`append_encodeList` and the four actual `EnumPerm.pack` forms to relate the
displayed words to `EnumPerm.genBlock`/`mpBlock` if a short symbolic adapter
fits. It must unfold only fixed cons syntax (not numerically evaluate huge
pairings), and supplies no internal contract via a Nat semantic theorem.
The essential checks are arbitrary-model suffix formulas, GEN at i=0 and
H=1, MP at A=1 and B=1, B=0 success with A≠1, generic contract composition,
and the major input top0/P A S. Audit both exact suffix laws and both
contract theorems. No assumption asserts an arbitrary false-target block.

## Exact prospective cache

`c222-command-rule-next-cache-plan-20261026.json` reauthenticates124 cached
custom modules, including95 Foundation,409 artifacts and38 external
boundaries (571 source/artifact/boundary observations). This adds just the
frozen candidate Leaf main to the accepted prior closure. Its provisional
source is `511e3e22251137fdcca7c779efa06092892990d39fdadb47777849f58cf02b88`;
primary `/tmp/command-leafperm222-controller-gw4_opuf/lib/DiophantineConsistency/ArithmeticCommandLeafPerm222.olean`
has SHA `4c1b5a76ccbdc5afc3c19a330aa574a7b33b2a73a038eb6ddcd1e51ea8317456`.
Root's Leaf acceptance is a prerequisite to implementation. Original Leaf
attempts, accepted root Block provider, and Composition provenance remain
unchanged. No new Foundation source/object is needed. Any subsequently
authorized build will be private, two fresh leaves only, with source/pin
reauthentication, preserved attempts, Lean4.32 resource caps and512MiB reserve.
