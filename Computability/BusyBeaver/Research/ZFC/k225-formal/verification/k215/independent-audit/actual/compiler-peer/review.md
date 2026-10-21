# Independent Rocq command-compiler source peer

Read all 560 lines of `rocqperm/EnumPerm.v`, `L1_SoundPerm.v`, `L1_CompPerm.v`, and `SeedPerm.v`, their four generated K215 counterparts, and the dominated-calculus interface `ThmDom.v`. Also read the relevant generator routing and numerical formula/stack definitions. No compiler or supplied generator was invoked, and no repository file was edited. I found no mathematical or concrete source/type-shape defect in these four new proofs. Elaboration remains pending in the build lane.

## Stack and zero-code contracts

`ax_stack` has exactly ten heads, in pop order: rho1, rho2, rho3, rho4, rho5, rho6, G, rho8, GEN of the cache, and saved current. It retains the arbitrary natural tail `w`. The soundness invariant covers current, cache, and every iterated decoded stack head; it does not require a canonical nonzero list encoding. The zero tail decodes to an infinite stream of truth code 0. `good_push` uses `unP_P`, so the alias `P(0,0)=0` is explicitly compatible with the invariant.

`DISCARD` first runs `MP 1` with cleared counter/cache. Its implication cannot be 0 because the right operand is positive, so failure sets current 0 and counter 1 without changing the stack. `AX` with c=a=1 then has current gate 0 and saves that current 0 as the tenth head; ten NIPs restore the original tail and clear cache/counter. No arbitrary original current is accidentally retained in the cleared result.

`J 0=[]` is essential: on cleared current/cache, `I(0,0)=0`, so a literal `MP 0` would succeed and add a saved zero. For positive u, `MP u` necessarily fails against cache 0 and sets the counter to u without that push. This is precisely the proof of `exec_J`.

For row selection, `DISCARD; J u; AX(c,a−u,b)` yields A=a when u≤a. After j NIPs the selected row is cached. DROP makes it current and pushes the old gate. Exactly 11−j further NIPs consume that gate plus the remaining ten−j AX heads, ending with the saved cleared 0 in cache. Rows are non-falsum by their outer implication/quantifier tags; the gate is either truth or a non-falsum bundle. Rho8 alone requires u≤a, matching `thmDom`. Other rows use u=0. Bundle selection instead retains the current gate and pops all ten heads, with both freshness premises explicit.

GEN preserves an arbitrary tail: the first DROP saves the compiled X and clears current; J sets the binder; NIP restores X to cache; AX emits `wal i X` as head nine while saving current 0 at head ten. Nine NIPs, DROP, and two NIPs produce the quantified current and restore the exact tail with cache/counter 0. Coincident labels make the current gate 0 and do not invalidate the generated row.

For MP, the two compiled subproofs restore exactly the tail they were given. The rearrangement recovers current A and cache I(A,B). If A=1, an intervening NIP already halts, which is allowed by `blk`; otherwise successful MP returns B, pushes a zero, and leaves counter B. AX at c=a=B resets both scratch registers and saves B as its tenth head. Ten NIPs recover B; DROP and two NIPs consume the gate/saved-zero pair and restore the tail. If B=1, the relevant NIP halts; otherwise it finishes normally. B=0, A=0, and zero tails are covered by pairing inversion, not excluded assumptions.

## Enumeration and seed

The first command reads its fields directly from `np`; later commands read `pl−1`. `fields` matches the actual order: NIP=0, DROP=1, MP=2 with x, AX=3+c with y then x. `step_read` treats both entry forms explicitly. Every nonempty prooflist step strictly decreases its numeric prooflist using `unP_le`; `drain` therefore reaches the next candidate or halts. No valid-command or theorem-stack premise is hidden in this reachability argument.

`START Y` is an AX command, so it resets counter/cache even for arbitrary retained current/cache/tail. The compiled falsum block tolerates the resulting arbitrary current and tail; the final DROP/NIP/NIP halts. The proof never assumes the preceding candidates left a clean theorem list for this completeness direction.

For seed 4, `START 4` has first-candidate encoding `P 3 (P 4 (P 1 r))`. Pairing bounds prove it is at least 4. `reach_from` then reaches that candidate from `seedPerm=(pl0,np4,tw0,ws0,d0,h0)` or halts earlier; `N−4` is justified by the bound. This is the needed cofinal padding argument, independent of any numerical size limitation on the compiled proof. The soundness direction separately proves the actual seed invariant.

## Generated-source boundary

The independent metadata reader verifies the four generated files are byte-exact copies of the reviewed originals after only the recorded hash header and `From NS Require`→`From K215F Require` substitution. All 42 generated K215 modules have an independently checked local namespace/import census: no active stale NS/K217F/K218F/K219F/K216F/K221F references, and every K215F import resolves to one of the 42 modules. This is not a claim of full proof rereview of all 42 files. Old variant names in inherited comments remain comments.

The compiler invokes `thmDom_of_thm222` to compile the dominated calculus, while soundness may use the unrestricted `thm222` constructors; this is the correct orientation. Actual proof checking of that transfer certificate and the complete endpoint remains part of the 237-module build, not an assumption introduced here.

## Build handoff

No repair suggestion is needed from this static pass. Preserve failed compiler attempts if elaboration finds a tactic issue. Require the existing final assumption reports and recursive `coqchk` from the endpoint audit; this ordinary/source review does not substitute for them.
