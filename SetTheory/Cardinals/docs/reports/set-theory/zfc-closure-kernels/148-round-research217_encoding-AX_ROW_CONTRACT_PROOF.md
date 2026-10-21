# Current205 AX emitter order: contract boundary

## Coverage, before a new search

The received K221/source208 fixed-closed-atom receipt reports all 40,320 permutations of eight rows, minimum208 nodes, and no nonidentity tie. Its source and machine are not the current205/218 pair. The receipt was read as inert data, not replayed. It therefore documents prior coverage of that old template, not current205 coverage and not a general lower bound.

The owned `ax_row_contract_inventory.py` now binds all eight current intervals on source SHA-256 b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9. Every row's literal primitive word and every guarded internal edge match its closed macro composition. Every row has no external entry into its interior, and returns only at its end. Both whole-source CFG resolvers agree. The current source decomposes into520 indivisible closed atoms in [135,2650), grouped67/88/58/61/64/61/72/49 by row. No permutation was searched by this inventory.

## All-natural arithmetic contracts

Write P(a,b)=(a+b)(a+b+1)/2+b. Scratch registers are R6,R7; parameter registers R4=a,R5=b,R3=c. All statements below allow arbitrary natural operands, including formula-code junk.

The ten-leaf pair core takes (R6,R1,R7)=(a,b,0) to (0,0,P(a,b)). Its initial transfer changes (R6,R7) to(a+b,b). At the subsequent outer decrement boundary R1=0. One complete iteration with R6=n>0 adds n to R7 and decreases R6 to n−1: the first decrement/add contributes1, the remaining n−1 units are transferred through R1, and the return transfer contributes n−1. Thus R7+tri(R6) is invariant at this boundary and R6 decreases. Inner transfers also decrease their tested register. This proves termination and the claimed value for all naturals.

The eleven-leaf unpair-Rj core starts R6=R7=0 and Rj=N. After i decrements of Rj, P(R6,R7)=i. One iteration maps(a,b) to(a−1,b+1) if a>0, or(0,b) to(b+1,0) if a=0. Both increase P by1. At Rj=0, the final transfer moves R7 to Rj and clears R7. Hence Rj=P(a,b) becomes R6=a,Rj=b,R7=0. Its main loop has exactly N iterations and all inner transfers terminate.

The nineteen-leaf PushOldTop first moves old R1=t to R6 and old R2=s to R1, applies the pair core, then transfers R7 into R2. It returns R1=0,R2=P(t,s),R6=R7=0. The seven-leaf copy-Rk duplicates parameter Rk into R1 and R6, then restores Rk from R6. Starting R1=R6=0, it produces R1=old Rk, preserves Rk, and clears R6. Their composition is the26-leaf push-a/b/c macro. PushOne is PushOldTop followed by CI1.

The27-leaf implication macro unpairs R2=P(a,s), pairs the popped a with old R1=b, and transfers four increments per unit from R7 into R1. It returns R1=4P(a,b),R2=s,R6=R7=0. Q,R,E append respectively2,1,3 increments to R1. Negation is PushOne then implication. Exists is negation, Q, negation. These constructors preserve all registers other than R1,R2 and scratch, and scratch returns to zero.

## Reader dependency is contained inside rho8

The exact [161,194) fourth-field load consists of PushOldTop at[161,180) and UnpairR8+MoveR6ToR1 at[180,194). Thus on arbitrary old top t, older stack s, R8=P(u,v), and zero scratch, it terminates with R1=u,R2=P(t,s),R8=v and zero scratch. It preserves R0 and all three parameter registers. It reads no other command field.

The other seven emitters never access R8. Moving the entire rho8 emitter, including this load, past any whole other emitter therefore leaves the final R8=v unchanged. It does not matter how many formulas are already on the stack when the load occurs: PushOldTop preserves that entire stack. Merely moving rho8's formula constructors while leaving its load behind would not have this contract and is excluded.

## Row composition and compiler boundary

Each row's bound postfix program starts by pushing a parameter or the contained field, never consumes below the preexisting top, and ends with exactly one generated formula on top, with the prior top and complete older stack preserved underneath. All rows preserve R0,R3,R4,R5 and return R6=R7=0. The inventory records exact formulas and current ordinal intervals. Their order is rho8,G,rho6,rho5,rho4,rho3,rho2,rho1.

The following gate constructor starts with another parameter push, so it saves the final row top before building the unchanged gate. The eight generated row formulas therefore occupy eight stack positions in reverse emission order. A permutation preserves their set, the older GEN/cache and previous-top entries, the gate value, the number of emitted formulas, and proof-list field consumption. It changes which named axiom occupies each of these eight positions. A completeness compiler must use the inverse permutation when retrieving a row; it may not inherit old numeric offsets. No ordinal-CFG equivalence between different row orders is asserted. The permitted source reconstruction instead preserves each closed atom's internal graph and transports the surrounding graph to the changed ordered atom sequence.

This is sufficient to justify a small syntax-price census. It is not a physical allocation or a completed new enumerator calibration. Any retained candidate still needs the explicit axiom-position/compiler bridge, decoder and primitive contracts, and blank startup.

## Proposed bounded next family

Keep rho8 first and rho1 last initially. There are five interior adjacent swaps: G/rho6, rho6/rho5, rho5/rho4, rho4/rho3, rho3/rho2. Reuse the current closed-atom concatenation template, not the old208 template. Hash-consed source costing and exact transported atom CFG checks for those five should take well under two seconds. No binary allocation is proposed unless a source costs at most205 or exposes a concrete reusable role. There are seven adjacent swaps in the full eight-row family, not eight; the two endpoint swaps are deliberately deferred.

## Completed approved census

The five proposed interior swaps were subsequently approved and executed. Costs were289,269,269,269,280 nodes, versus the205-node identity. Every candidate retains4,744 primitive occurrences and passes exact closed-atom edge/exit transport, unchanged outside CFG, and both complete CFG resolvers. Explicit named-axiom stack positions are recorded in AX_ADJACENT_PRICES.json. The run took0.316seconds and19,952KiB peakRSS. No candidate reached the physical-allocation gate, and no binary allocator or wider permutation family was run. These are costs for the fixed current520-atom skeleton, not a lower bound for all emitter-level associations.
