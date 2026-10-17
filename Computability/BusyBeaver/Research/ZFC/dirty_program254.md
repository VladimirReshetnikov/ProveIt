# Safe dirty starts for the existing structured program

The source 35 report supplies two useful new Lean modules: cofinal safe
starts for the exact enumerator, and an absorption map for arbitrary
initial selector and scratch fields at the root of the published 219-node
structured program. `EnumSafeStart254.lean` and `DirtyRoot254.lean` are
attributed ports of those supplied proofs, preserving their statements.
The original files remain in the intake collection as
`code/35-dirty-formal-src-BusyBeaver-ZFC-EnumSafeStart254.lean` and
`code/35-dirty-formal-src-BusyBeaver-ZFC-DirtyRoot254.lean`.
Their arrival is `4e720ccbbfaa836b95be3b2f3f268a737b48c6d1`, their
placement is `6135ffef4b`, and their ProveIt source pin is
`426592ce97e52d309bfb8f0132411556650b7ac1`. The ordinary cofinal-padding
argument was already recorded in intake source 09; source 35 adds its
checked Lean proof. The literal program is attributed to Mira-Cult,
Jeff Ketchersid and Andrew James Wade, at busy-beaver pin
`297ab8df7e5de329605c3875b4934643b371a5e3`.

`DirtyProgram254.lean` supplies the current-tree composition that was
explicitly left open in the submitted report. Write the nine register
fields in declaration order as

```text
[N,T,W,A,D,H,X,Y,L]
 nextproof, top formula, stack, selector, numeric parameter,
 retained formula, scratch1, scratch2, current proof list.
```

If `L=0`, put `(N',X',n)=(N+X+1,0,N)`; otherwise put
`(N',X',n)=(N,X,L−1)`. With `(u,v)=unP(P(X',Y)+n)`, the virtual clean
root state is

```text
[N',T,W,0,D,H,0,0,P(A+u,v)+1].
```

Both actual root prefixes, fetch133 followed by selector-read174, finish
at exactly `[N',T,W,A+u,D,H,0,0,v]`. The common tail is the same literal
program, so every structured exit and resulting full register file agree.
In particular iterated-root halting agrees, with no premise about the
formula fields. The zero selector and scratches identify the virtual
state with `L2.toAS` of its six-field enumerator state. Current
`L2.iter_iff` therefore supplies the exact absorbed enumerator comparison.

The source's `complete_from` says that a numerical refutation forces the
enumerator to halt from any six-field state. It first drains an initial
proof-list pointer, then reaches all later candidates unless already
halted. A reset AX command has an unused padding field that makes a
compiled contradiction candidate exceed the initial cutoff while
retaining its execution contract. Composing this with absorption gives
`DirtyProgram254.complete_from` for all nine initial numeric fields,
without a formula invariant.

For the converse, the exact existing invariant remains essential:

```text
Safe st := Enum254.Inv (DirtyRoot254.enumOf st)
        ↔ C254 st.tw ∧ C254 st.p2 ∧ Enum254.Good st.ws.
```

`Good` checks theoremhood of the head at every stack tail. No condition
is imposed on `N,A,D,X,Y,L`. Under `Safe`, the new module proves

```text
IterHalts dag254 (L2.enc st)
  ↔ C254 F
  ↔ BProv NativeTheory254.NativeAx [] Bottom.
```

The second equivalence is the existing exact native-theory interface.
Its GIC schema contains every actual native `Form` matrix and universally
closes the parameters; it is not an arbitrary external relation schema.
The corresponding consistency/nonhalting statement is the exact
contrapositive. `six_nonformula_iff` displays all six unrestricted fields
explicitly with the three known safe zero formula fields:

```text
IterHalts dag254 (L2.enc ⟨N,0,0,A,D,0,X,Y,L⟩)
  ↔ BProv NativeTheory254.NativeAx [] Bottom.
```

`RMEquiv254.path_halts_iff_iter` transports these contracts to Wade's
path semantics of the **219-node** `RMEquiv254.pathDag254`, starting at
the empty instruction pointer. The module does not identify this path
program with the separately listed 6,459-node `Prog254` program.

`L2.enc` retains its zero tail at every logical register index at least
9, recorded by `enc_tail`. Neither the nine-field theorem nor its path
corollary allows an arbitrary interior instruction pointer or an
arbitrary binary tape. A binary initializer must still reach a valid
whole dispatch frame at the genuine root, with the stated head, machine
state, exterior tape, and spare-block data. Physical spare blocks and
the logical zero register tail are separate resources. No new blank
initializer, smaller machine, general binary-runtime theorem, ZFC
calibration, or arithmetized proof-code transformation follows here.

The three modules compile with the explicit official Lean 4.32.0
executable in 0.53, 0.62 and 0.31 seconds. Thirty-four theorem assumption
audits and four caller examples pass in 0.40 seconds; only `propext`,
`Classical.choice` and `Quot.sound` occur. The callers cover unconditional
halting from a native refutation, all six arbitrary nonformula fields,
exclusion of every safe dirty path start by a supplied native model, and
exact preservation of every structured exit's full register file. The
composition also received an independent read of its source and scope.

Commands, exact caller source and audited axiom sets are recorded in
`results/dirty-program254-verification.json`. This scoped check reused the
source-verified 93-module dependency cache and compiled only the three new
modules; it did not rerun the large blank bootstrap. The preserved intake
reports and their evidence remain unchanged.
