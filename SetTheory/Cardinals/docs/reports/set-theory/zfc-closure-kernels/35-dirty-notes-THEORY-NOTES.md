# Exact absorption of arbitrary initial control registers

## Result and its purpose

The new proof in `BusyBeaver/ZFC/DirtyRoot254.lean` removes the restrictions
`axiomcode = scratch1 = scratch2 = 0` from the **register-machine root
configuration** of the literal 219-node `dag254`. It does so by an explicit map
to a clean root configuration that has exactly the same continuation. This can
enlarge the set of acceptable outcomes of a shorter blank-tape initializer.
The theorem does not establish that any particular shorter initializer reaches
such a configuration.

The exact continuation theorem quantifies over all nine register values and
does not assume consistency, theoremhood, a full axiom-block simulation, or a
halting equivalence between the DAG and the abstract enumerator. It preserves
every structured exit and its exact resulting register file. A corollary
preserves `RMDag.IterHalts`.

The companion `EnumSafeStart254.lean` formalizes the already known ordinary
tail-universality argument: an inconsistent code calculus forces the abstract
enumerator to halt from every starting state, and its usual theorem invariant
gives the converse. The ordinary argument is explicitly present in ProveIt's
`intake-144-source-09-theory.md`, finding 5. The new contribution here is its
checked Lean formulation and the separate exact arbitrary-scratch absorption
theorem, not discovery of ordinary cofinal padding.

## Sources and attribution

The ProveIt input is commit
`426592ce97e52d309bfb8f0132411556650b7ac1`.
The upstream busy-beaver input is commit
`297ab8df7e5de329605c3875b4934643b371a5e3`.

The relevant existing ProveIt files are:

- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Enum254.lean`:
  the exact six-field enumerator, invariant, reset/compiler contracts, and
  zero-start endpoint.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Control254.lean`:
  `fetch_pos` has no scratch premise; `fetch_zero` requires `scratch1 = 0`.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Macros254.lean`:
  `loop115` already proves general nonzero-scratch unpairing. Other copy loops
  give the required general register effects.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMDag.lean`:
  exact structured semantics, determinism, and repeated-root halting.
- `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-144-source-09-theory.md`:
  finding 5, headed **Tail universality**, explicitly checks arbitrary retained
  data, arbitrary numerical cutoff, and the four-field padded reset command.

The upstream clean-boundary bridge is
`ZF/m254/coq/prog/L2Root254.v`. Its `enc` puts the enumerator's six fields in
registers 0, 1, 2, 4, 5, 8 and sets registers 3, 6, 7 to zero.
`root_sem` quantifies over every enumerator state. `iter_halts_dag` states

```coq
Theorem iter_halts_dag s R :
  approx R (enc s) -> iter_halts dag254 R <-> halts_from s.
```

Thus it is not limited to the usual initial `nextproof = 2` configuration.
`approx` in `ProgLib254.v` is `forall i, R i = get m i`; it is equality at all
register indices, including the zero tail, and must not be described as
silently allowing arbitrary higher-register values. `Main254.v` subsequently
specializes the bridge to the actual blank-boot endpoint. This source review
does not constitute a fresh Coq rebuild of the upstream development.

## Exact nine-register statement

Write the initial register tuple in literal numeric order as

\[
 r=(N,T,W,A,D,H,X,Y,L)
   =(r_0,r_1,r_2,r_3,r_4,r_5,r_6,r_7,r_8).
\]

These are `nextproof`, `topwff`, `wffstack`, `axiomcode`, `param1`,
`param2`, `scratch1`, `scratch2`, and `prooflist` respectively.
Let

\[
 P(x,y)=y+\frac{(x+y)(x+y+1)}2,
 \qquad \operatorname{unP}=P^{-1}.
\]

Define

\[
 (N',X',n)=
 \begin{cases}
   (N+X+1,0,N),&L=0,\\
   (N,X,L-1),&L>0,
 \end{cases}
 \qquad (u,v)=\operatorname{unP}(P(X',Y)+n).
\]

The **virtual clean root** is

\[
 V(r)=(N',T,W,0,D,H,0,0,P(A+u,v)+1).
\]

All quantities are ordinary natural numbers. There are no restrictions on
`N,A,D,X,Y,L`; the exact continuation theorem also imposes no restrictions on
`T,W,H`. The Lean representation `L2.enc` sets every register above index 8 to
zero.

Starting at DAG root node 0, both `r` and `V(r)` reach the same tuple

\[
 (N',T,W,A+u,D,H,0,0,v)
\]

after the fetch node 133 and selector-read node 174, before node 175. Node 0
is `(133,139)`, node 139 is `(174,140)`, and node 140 is `(175,141)`. Therefore
the remaining program is literally the same continuation with literally the
same register file.

The named checked endpoints are:

```lean
theorem root_equiv (st : AS) : ∀ x Q,
  Run dag254 (.node 0) (L2.enc st) x Q ↔
    Run dag254 (.node 0) (L2.enc (virtual st)) x Q

theorem iter_equiv (st : AS) :
  IterHalts dag254 (L2.enc st) ↔
    IterHalts dag254 (L2.enc (virtual st))
```

### Why the dirty-prefix formula is correct

When `L = 0`, node 194 transfers `N` into both `prooflist` and `scratch1`;
the latter starts with `X`, so it becomes `N + X`. Node 203 transfers that
value back to `nextproof`, and the increment gives `N + X + 1`. Scratch2
retains `Y`. When `L > 0`, fetch simply decrements `L`.

Node 115 runs the inverse Cantor successor walk from its *current* scratch
pair. Consequently, starting from `(X',Y)` and executing `n` steps yields
`unP(P(X',Y)+n)`. Node 209 moves its second component into the proof-list
register. Node 201 adds its first component to the existing selector register
`A` and zeros scratch1. In particular, the initial selector is an additive
offset **after** unpairing. Replacing the initial code by `n + P(A,0)` would
be incorrect.

For `V(r)`, its nonzero proof list is decremented to `P(A+u,v)`, and the clean
read produces selector `A+u` and tail `v`. This proves equality at the stated
boundary. The generic `node_transfer` lemma handles all structured outcomes.
For a continue exit, equality of the resulting restart register file allows
the identical recursive derivation to be reused; it does not assume that a
node never restarts.

## Safe formula data and consistency calibration

The abstract enumerator's invariant is

\[
 \operatorname{Safe}(T,W,H)
 := C_{254}(T)\land C_{254}(H)\land\operatorname{Good}(W),
\]

where `Good(W)` means that every formula obtained from the encoded stack by
successive tail operations is a theorem of the numerical code calculus.
The invariant places no condition on the numerical proof-list pointer,
enumeration cutoff, or retained parameter `D`. In particular, `T=W=H=0` is
safe, since code 0 is the calculus's truth code and the empty stack has only
truth in its implicit tail.

The Lean theorem

```lean
theorem safe_start_iff (s : Enum254.St) (hs : Enum254.Inv s) :
  HaltsFrom s ↔ C254 F
```

has all six starting fields quantified. Its completeness half is stronger:
`complete_from (s) : C254 F → HaltsFrom s` has no invariant premise.

For completeness, a finite positive proof-list pointer drains unless a
halting command occurs first. Every later candidate code is eventually
visited. A compiler-produced contradiction block can be preceded by
`CAX(0,1,1,U)`, which resets the retained parameter and cache for arbitrary
incoming values. Its compiled list code is

\[
 P\bigl(3,P(1,P(1,P(U,\tau)))\bigr)\ge U,
\]

where `τ` is zero for an empty remaining list and otherwise the remaining
list's code plus one. Choosing `U` to be the initial cutoff places the whole
reset-and-refutation program in the part of the enumeration that remains.
The compiler contract quantifies over every current formula and stack, so it
applies to whichever state arrives there. The terminal
`DROP(0), NIP(0), NIP(0)` sequence turns the derived falsity into the halting
condition. Soundness is the ordinary invariant preservation argument.

`V(r)` preserves `T,W,H`, so it preserves this invariant. Combining (i) the
exact dirty-to-clean root equivalence, (ii) the upstream clean-boundary
DAG/enumerator theorem, and (iii) tail universality yields the ordinary
mathematical corollary: **every actual root configuration with safe formula
data has the same halting/consistency calibration, for arbitrary values of
the other six registers**. The existing code-calculus/ZFC calibration then
identifies this with inconsistency of ZFC.

The new Lean files do not assert that this whole composition is already a
single checked Lean endpoint. `virtual_enum_iff` deliberately names the
*abstract enumerator* of the virtual state. Completing the existing Lean
axiom-block and clean-root bridge remains a separate obligation; the upstream
Coq theorem is not imported as an unannounced Lean axiom.

## Implication for a smaller-machine search

A candidate initialization certificate may now target any decoded root frame
with safe `(T,W,H)` instead of insisting that all scratch and selector fields
are zero. The allowed numerical cutoff is arbitrary, so increasing
`nextproof` during initialization is also harmless. This relaxation is
algorithmically useful because the cheapest unary register framing can contain
unintended positive register values.

It remains necessary to establish the physical binary tape representation,
head location, machine state, genuine root program counter, and the retained
decoder/program conditions for each candidate. The theorem is not an
arbitrary-tape theorem, does not validate an interior control location, and
does not itself reduce a transition table's number of states.

## Verification and reproducibility

The modules were compiled with Lean 4.32.0, compiler commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, against freshly compiled source
imports from the pinned ProveIt checkout. The `CheckTheory254` companion
records exact types and axiom audits. The main theorems use only the standard
Lean axioms `propext`, `Classical.choice`, and `Quot.sound`; `pad_code_ge` requires only
`propext` and `Quot.sound`. There is no `sorryAx`, admission, new
axiom, or external-decision oracle.

To rebuild from this directory with an existing ProveIt checkout and a Lean
4.32.0 executable:

```sh
python3 verify_theory.py --repo /path/to/ProveIt --lean /path/to/lean --build-dir build
```

The checker compiles all transitive source imports into an isolated directory,
then the two theorem modules and statement-audit module. It records exact
commands, source hashes, compiler version, repository revision, exit statuses,
and per-module output in `build/theory_audit.json` and adjacent `.log` files.
It does not modify the checkout or fetch dependencies.

For an already compiled dependency directory `build`, the two core commands,
executed from the directory containing this note, are:

```sh
LEAN_PATH=/absolute/build /path/to/lean -o /absolute/build/BusyBeaver/ZFC/EnumSafeStart254.olean BusyBeaver/ZFC/EnumSafeStart254.lean
LEAN_PATH=/absolute/build /path/to/lean -o /absolute/build/BusyBeaver/ZFC/DirtyRoot254.olean BusyBeaver/ZFC/DirtyRoot254.lean
LEAN_PATH=/absolute/build /path/to/lean -o /absolute/build/BusyBeaver/ZFC/CheckTheory254.olean BusyBeaver/ZFC/CheckTheory254.lean
```

The sixteen existing source modules in the transitive import closure are
`FirstOrder.Fol` and, under `BusyBeaver.ZFC`, `Kalmar`, `TarskiCalculus`,
`TarskiDerived`, `TarskiLeibniz`, `TarskiClean`, `TarskiComplete`, `Lukasiewicz`,
`TarskiFalsity`, `Code254`, `Enum254`, `RMDag`, `Dag254`, `L2Lib254`,
`L2Macros254`, and `L2Control254`. The import graph determines their order.
