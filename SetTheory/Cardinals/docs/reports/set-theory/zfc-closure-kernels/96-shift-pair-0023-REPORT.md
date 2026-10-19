# Shifted binary pairing: exact logical and enumerator transfer

## Result and limits

Replacing every logical, theorem-stack, proof-payload, and command-list Cantor pair by

    E(a,b) = 2^a (2b+1) - 1

preserves the exact ordinary first-order comparison theory and the proof-search calibration described below. In particular the target stays `F=1`, the logical seed stays `(N,T,W,A,D,H,X,Y,L)=(3,0,0,0,3,0,0,0,0)`, and the abstract changed enumerator halts from this seed exactly when ZFC has a finite refutation. This is a mathematical transfer theorem, not a newly kernel-checked theorem or a claim that a smaller binary machine has been compiled.

There is a real subtlety: the original bundle uses the same natural `c` both as a formula code and as a variable label. An ordinary recursive code bijection does **not** transport that bundle rule or its gate directly. The proof here goes through the unchanged native first-order theory using explicit own-code freshness and matrix adapters. It does not claim equality of the old and new sets of numerical theorem codes.

The remaining implementation obligations are: establish the changed source's clean-register macro contracts and command semantics, produce/count an actual table, prove its complete-frame positive-time simulation, and verify its own exact blank bootstrap. The original Cantor dirty-scratch contracts cannot simply be reused. A source or compiler cost estimate alone supplies none of these endpoints.

### Prior attempt

The supplied source-search packet already contains `pairing_backend_experiment.py`. It tests the *unshifted* operation `2^a(2b+1)`, including incompatible mixed encoder/decoder variants. It changes the relation-zero target to 5, adds a zero-unpair guard, and explicitly states that no proof-search calibration or whole-program theorem is supplied. That is not the shifted bijection above. This report neither executes that script nor imports any downloaded project code.

The current numerical calculus already contains the Łukasiewicz single implication axiom and already derives the translated IR identity. No IR row is deleted in this route.

## 1. A sufficient generic pairing interface

Let `p : N×N→N` and `u : N→N×N` satisfy:

1. `u(p(a,b))=(a,b)` and `p(u(n).1,u(n).2)=n`
2. `p(0,0)=0`
3. `a≤p(a,b)` and `b≤p(a,b)`

For the effective proof-checker and enumerator claims also require `p,u` to be computable. For the stronger primitive-recursive coding assertions require them to be primitive recursive, as the concrete shifted functions are. The purely semantic generic theorem does not require this additional effectivity assumption.

Consequently `p(a,b)=0` iff `a=b=0`; both inverse fields are at most their input. These are the generic properties used by the formula, native-theory, proof-certificate, and command-enumeration arguments below. Actual helper termination and frame preservation are separate implementation properties.

For `E`, unique factorization of the positive integer `n+1` gives

    a = v2(n+1)
    b = ((n+1)/2^a - 1)/2.

This proves both inverse equations, including `u(0)=(0,0)`. Equivalently, repeatedly remove a trailing binary one from `n`; their number is `a`, and the first even remainder divided by two is `b`. Each odd step sends a positive `n` to `(n-1)/2<n`.

The identities

    E(0,b)=2b
    E(a+1,b)=2E(a,b)+1

give a direct terminating encoder by induction on `a`. More quantitatively,

    E(a,b)=2^(a+1)b+(2^a-1) ≥ 2b+a ≥ a+b,

because `2^a≥a+1`. Thus the generic field bounds hold. They must not be replaced by an incorrect universal *strict* bound: `E(1,0)=1`. Precisely:

- The second inverse field is at most `floor(n/2)`, hence is strictly below `n` for every positive `n`
- The first inverse field equals `n` only at `n=0` or `n=1`; otherwise it is smaller
- Both fields are strictly below `p(a,b)+1`, which is the bound needed for successor-delimited proof-list tails
- `E(a,b)=a+b` only at `(0,0)` and `(1,0)`

The generic theorem does not need the stronger tail bound. Its original decrement-before-unpairing supplies strict decrease even for a pairing whose second field can equal its input.

## 2. Exact numerical syntax and calculus

For a fixed pairing `p`, retain the four tags:

    I(A,B)=4p(A,B)
    R(i,j)=4p(i,j)+1
    Q_i(A)=4p(i,A)+2
    Eq(i,j)=4p(i,j)+3
    F=1=R(0,0)
    N(A)=I(A,F)
    A & B = N(I(A,N(B)))
    D_i(A)=N(Q_i(N(A))).

These are arithmetic operations on natural numbers, not constructors of a free term algebra. In particular `I(0,0)=0`. The exact eight logical row families are:

    rho8(a,b,c,u) = ((c→u)→a)→((a→c)→(b→c))
    rho7(a,b,c)   = Eq(c,a)→(Eq(c,b)→Eq(a,b))
    rho6(a,b)     = D_a(Q_a(b))→b
    rho5(a,b,c)   = Eq(c,a)→(R(c,b)→R(a,b))
    rho4(a,b,c)   = Q_a(Q_b(c))→Q_b(Q_a(c))
    rho3(a,b,c)   = Eq(a,b)→(R(c,a)→R(c,b))
    rho2(a,b,c)   = Q_a(b→c)→(Q_a(b)→Q_a(c))
    rho1(a,b)     = D_a(Eq(a,b)).

An arrow here means `I`, and `&`, `N`, `D` mean the displayed numerical operations. The container and global-image expressions are exactly:

    C(a,b,c) = D_b(
      Q_a(R(a,b) →
        (D_c(Q_b(Q_c(R(c,b)→R(c,a)) → R(b,c)) & R(c,b))
         & Q_c(R(c,a)→R(c,b))))
      & R(c,b))

    G(a,b,c) = D_c(
      Q_a(R(a,b) → Q_b(c → D_b(c & R(b,c))))
      & Q_b(R(b,c) → D_a(c)))

    beta(a,b,c) = (C(a,b,c) & G(a,b,c))
      & ((R(a,b)→Q_c(R(a,b))) & (Eq(a,b)→Q_c(Eq(a,b)))).

All formula-valued occurrences of the bare `c` in `G` really are the number `c`; occurrences as a subscript remain variable labels. The bundle axiom gate is exactly `c≠a ∧ c≠b`; no `a≠b` gate is added.

Define `C_p(n)` to be the least predicate with these constructors:

- Truth: `C_p(0)`
- MP: `C_p(A)` and `C_p(I(A,B))` imply `C_p(B)`
- GEN: `C_p(A)` implies `C_p(Q_i(A))` for every `i`
- All eight row families above
- `C_p(beta(a,b,c))` when `c≠a` and `c≠b`

The shifted calculus is `C_E`. No nonlogical axiom or logical rule is removed. The old numerical calculus is the same definition instantiated with dual Cantor pairing.

### Decoding, zero, and strict-subcode termination

Decode zero as `T0=(R(0,0)→R(0,0))` in ordinary named first-order syntax. For positive `n`, put `(a,b)=u(floor(n/4))` and read the remainder modulo four as implication, relation, universal quantification, or equality respectively. Decode the formula-valued children recursively; labels are not recursively decoded.

For `n>0`, both fields satisfy `a,b≤floor(n/4)<n`. Every recursive formula child therefore has smaller numerical code. This justifies structural recursion, or the existing fuel implementation with fuel `n+1`; extra fuel beyond `n` does not change the result. There is no nontermination at the numerical fixed point `I(0,0)=0`, since zero is a base case.

For implication other than `(0,0)`, decoding commutes syntactically. For `(0,0)`, the two syntactic readings are `T0` and `T0→T0`, which are both true in every structure and every valuation. Hence the semantic implication equation holds uniformly. Decoding `R`, `Eq`, and `Q` commutes syntactically in every case. `dec(F)=R(0,0)`.

Encode ordinary named formulas recursively using the four numerical operations; encode genuine bottom as `F`. Every actual named formula has positive code. This follows by induction, since atomic and quantifier tags are positive and an implication whose children have positive codes has positive paired payload. Thus the code-zero truth alias is not silently treated as the literal image of a finite ordinary formula. In irreflexive structures the encode/decode round trip preserves truth, including genuine bottom and binders at variable zero.

### Free variables and quantifier indices

The exact syntactic tests are the usual named-variable tests: atoms have the indicated two free labels; implication takes their union; `Free(i,All(j,A))` means `i≠j ∧ Free(i,A)`; genuine bottom has none. `Occurs` additionally includes every binder label. They are properties of the decoded/encoded finite syntax, not extra source-machine oracle tests.

Induction gives two different required bounds:

1. If `i` occurs in an actual named formula `f`, then `i<enc_p(f)`
2. If `c>0` and `i` occurs anywhere in `dec_p(c)`, then `i<c`

For (1), use `a,b≤p(a,b)` and the positive tags; implication combines positive child codes. For (2), use the strict decoded field bound, descending through each positive child. A nested zero child introduces only the label zero, which is still below the positive ancestor.

At code zero, the blanket syntactic assertion is false: label zero is free in `T0`. The correct uniform semantic statement is

    if valuations e,e' agree below c,
    Sat(e,dec_p(c)) iff Sat(e',dec_p(c)).

For positive `c` use (2); for zero use that `T0` is a tautology. Consequently updating the valuation at label `c`, even underneath arbitrary updates at labels `a` and `b`, does not affect the truth of `dec_p(c)`. No irreflexivity assumption is needed for this freshness lemma. This is precisely the property required by the code-as-binder GIC expression.

Global irreflexivity *is* needed to interpret the relative falsity alias under all valuations, including beneath `Q_0`. It validates `N`, `&`, and `D` as negation, conjunction, and existential quantification. Quantifying variable zero is not avoided or silently renamed.

## 3. The unchanged first-order comparison theory

Let `NativeAx` be exactly the inherited first-order predicate from `NativeTheory254.lean`: universal closures of the fixed native container formula, of `gicForm(phi)` for **every actual finite native formula phi including equality and all parameters**, and of `∀x(x∈x→bottom)` with genuine bottom. It is not a schema over arbitrary semantic relations and not an equality-free restriction.

Write `Ref(NativeAx)` for `BProv NativeAx [] bottom` in the unchanged ordinary first-order proof system. The generic coding theorem is

    C_p(1) iff Ref(NativeAx).

Here and below nonempty models are expressed with an explicit valuation `N→V`, so the empty-domain loophole is absent. The proof is as follows.

### Native models imply sound decoded-bundle models

A native model supplies global irreflexivity, containers, and every actual GIC matrix. All eight rows, GEN, MP, and truth are sound after decoding by the semantic constructor equations. Atomic vacuity uses exactly the two gate inequalities.

For `C(a,b,c)`, the inherited named container proof is coding-independent. Its possible `a=b` collision is retained: the forward premise then asks for `x∈x` and is false by irreflexivity. For `G(a,b,c)` with distinct `a,b`, apply actual native GIC to the native translation of the named matrix `dec_p(c)` with distinguished input/output labels `a,b`. Own-code semantic freshness from Section 2 makes the newly bound container label `c` harmless. The gate preserves its separation from `a,b`. For `a=b`, use the actual bottom-matrix GIC instance to obtain an empty image; the forward clause is vacuous by irreflexivity and the support clause is vacuous by emptiness. Thus every gated decoded bundle is true without introducing a new gate.

It follows that `C_p(1)` rules out every model of `NativeAx` with a valuation. Ordinary first-order completeness gives `Ref(NativeAx)`.

### Encodable-bundle models imply native models

Define the exact comparison predicate

    EncBundle_p(f) iff BotFree(f) and
      exists a,b,c: c≠a and c≠b and enc_p(f)=beta(a,b,c).

Assume a nonempty irreflexive structure satisfies every such actual named formula. The fixed named bundle at `(a,b,c)=(2,3,1)` with matrix `R(0,0)` is an encodable bundle because `enc_p(R00)=1`. Its container projection supplies precisely the native container property. The fixed labels and gates are unchanged.

For an arbitrary actual native matrix `phi`, use the inherited hygienic name conversion: free de Bruijn slot `i` at depth zero gets odd name `2i+1`; the newly bound variable at depth `d` gets even name `2d`, and the prior name map shifts under that binder. Genuine bottom becomes literal `R00`; logical operations use the relative-falsity abbreviations. This conversion is bottom-free and preserves truth in an irreflexive structure, including binders at name zero. The two distinguished free slots become names 1 and 3, and remaining parameters use 5,7,9,... .

Let `f` be that named matrix and pad it as

    pad(f) = ((f→f)→f).

Classically `pad(f)` and `f` have identical truth under every valuation. Let `c=enc_p(pad(f))`. Positivity of `enc_p(f)` and the field bounds give `c>3`; the occurring-label bound gives `not Free(c,pad(f))`. Hence the actual named bundle

    namedBundle(1,3,c,pad(f))

has encoding exactly `beta(1,3,c)`, is bottom-free, and satisfies both gates. Its G projection provides the native GIC instance for `phi`, with all parameters. Updating name 3 first to the domain and then to an output value is justified by overwrite; updating the auxiliary name `c` is harmless by the proven freshness. This proves every `NativeAx` axiom. The conversion concerns actual syntax and uses an explicit witness from the valuation for unused parameter slots.

### Relative-falsity completeness still works

The Łukasiewicz row proves the same polymorphic K, S, and Peirce laws for the operation `I`; no injectivity of implication is used. Row 6 then proves `F→A` for every numerical `A`. These give conjunction projection and the gated atomic-vacuity rules from the actual bundle.

Ordinary completeness over `EncBundle_p` plus genuine IR can therefore be translated to the relative-falsity Tarski calculus and then encoded into `C_p` rule by rule. Genuine IR translates exactly to `Q_0(I(F,F))`, a generalized identity already derivable from the Łukasiewicz row, MP, and GEN. No new IR row is required. At shifted pairing this code is `Q_0(I(1,1))=162`, whereas its old Cantor code was 610. These different numerals encode the same translated ordinary tautology; neither is the unaltered ordinary IR sentence.

Thus a native refutation excludes every irreflexive `EncBundle_p` model with a valuation and yields `C_p(F)`. This proves the converse direction and the generic theorem.

### Why direct recoding of old bundle parameters is invalid

Old `R(1,1)` has Cantor code 17; its shifted code is 21. The old bundle at `(a,b,c)=(21,22,17)` passes its gate. Replacing its matrix code by 21 while leaving variable labels alone gives `c=a`, so the new bundle gate fails. More generally recursively recoding formula arguments retains the old binder label `c`, whereas a newly generated bundle binds the new matrix code. The proof above avoids this obstruction by freshly constructing encodable bundles for each native matrix. It does not call the failed direct transformation a proof isomorphism.

## 4. Exact finite proof predicates

The raw proof data has the same twelve cases: truth, MP with an explicit output code and two child proofs, GEN with a binder and child proof, eight row leaves, and a bundle leaf. Its conclusion function uses the exact formulas of Section 2. Validation recursively checks children, checks the MP major conclusion equals `I(minorConclusion,output)`, and checks both bundle inequalities. All other row leaves are valid. This gives a decidable predicate with

    C_p(n) iff exists a finite valid raw proof with conclusion n.

If natural-number certificates are wanted, keep the original positive base-12 node code `12*payload+tag+1`, tags 0 through 11 in that case order. Replace each payload pair by `p`: MP payload is `p(output,p(quote(minor),quote(major)))`, GEN payload is `p(binder,quote(child))`, and row/bundle payloads are right-associated parameter tuples. The truth certificate is 1 and certificate zero is invalid. Decode with the inverse and the original fuel-limited parser; every recursive child is at most the payload and strictly below its enclosing positive node code. Structural height is at most quote code, and parser/quote round trip follows by induction.

Consequently the new checker is an exact finite proof predicate, not merely a semantic assertion. The ordinary native and ZFC proof predicates remain unchanged. Old and new numerical refutations can also be effectively translated by enumerating and checking target raw certificates until a proof of 1 is found; the theorem in Section 3 guarantees termination on valid input refutations. This is a partial-recursive-on-arbitrary-input/total-on-valid-refutations translation, not a claimed primitive-recursive direct field recoder or a supplied serialized ZFC proof object.

For the concrete shifted pairing, all displayed coding functions are primitive recursive except the unrestricted search translator just mentioned. Every proof-certificate validation, finite constructor evaluation, bounded parser, and finite command encoding terminates. Very large intermediate numbers are a time/space cost, not a logical partiality.

## 5. Exact theorem-stack and command encoding

The theorem stack is a stream represented by `p(top,tail)`, **without** adding one. The number zero is the all-zero stream, and `p(0,0)=0` makes pushing zero onto that stream invisible. This is intentional. `Good_p(S)` means every head reached by any finite number of inverse-tail operations satisfies `C_p`; zero is good by truth. For shifted pairing every positive stack tail is strictly smaller, so every numeric stream eventually reaches the all-zero stream. Soundness only needs the head/tail/cons equations, not this stronger termination fact.

The command selectors and field interpretation are unchanged:

    0: MP(x)
    1: DROP(x)
    2: NIP(x)
    c+3: AX(c;x,y,u).

With `r` the remaining-list pointer, pack them by

    pack(MP(x),r)   = p(0,p(x,r))
    pack(DROP(x),r) = p(1,p(x,r))
    pack(NIP(x),r)  = p(2,p(x,r))
    pack(AX(c;x,y,u),r) = p(c+3,p(x,p(y,p(u,r)))).

The encoding of a nonempty command list uses `r=0` at the final command and `r=1+code(remaining nonempty list)` otherwise. This is a different convention from the theorem stack. The first command of a candidate is read directly from the candidate number; later commands are read from `pl-1`. These successor delimiters prevent a suffix ending in a zero-coded command from disappearing. The single command `MP(0)` can have candidate code zero; this does not hurt completeness or the later cofinal padding argument.

At each main-loop boundary use `(pl,np,t,S,d,h)`. If `pl=0`, the fetch uses candidate `np` and increments `np`; otherwise it decrements `pl` and keeps `np`. Inverse-pairing the fetched code reads the selector and fields. On working registers `(t,S,d,h)` the effects are exactly:

- MP(x): put `d'=d+x`. If `I(t,d')=h`, set `(t,S,d,h)=(d',p(0,S),d',0)`; otherwise set `(0,S,d',0)`
- DROP(x): set `(h,p(t,S),d+x,h)`
- NIP(x): halt iff incoming `h=1`; otherwise set `(t,u(S).2,d+x,u(S).1)`
- AX(c;x,y,u): let `a=d+x`, `b=h+y`. Push old `t`, then `Q_a(h)`, then `rho8,...,rho1` in that bottom-to-top order. Set current `t=beta(a,b,c)` if the gate passes and `t=0` otherwise. Clear `d,h`

The new proof-list pointer is the packed suffix. All tuple inversions are total. For a nonempty current pointer, each residual pointer is at most `pl-1`, hence strictly below `pl`. Thus every candidate drains after finitely many nonhalting commands, regardless of formula values, and each exhausted candidate increments the counter once. The abstract command itself is a total finite arithmetic operation unless it deliberately halts at NIP.

## 6. Both enumerator halting directions, including the actual seed

Preserve the invariant

    C_p(t) and C_p(h) and Good_p(S).

MP uses the exact equality it tests; failure produces truth. DROP/NIP only move proved formulas; AX produces GEN of the cache, all eight axiom rows, and either a valid gated bundle or truth. A halting NIP therefore implies `C_p(1)`.

For completeness, use `Build(A)` with the following exact contract: from any `(t,S,d,h)=(T,S,0,0)`, the block either already halts or ends at `(A,S,0,0)`. Old stack and old current formula are arbitrary. Every unprinted field below is zero:

    Discard: MP(1); AX(1;0,0,0); NIP^10
    Bundle(a,b,c): Discard; AX(c;a,b,0); NIP^10
    Row rho_j: Discard; AX(c;a,b,u); NIP^j; DROP; NIP^(11-j)
    GEN_i from A: Build(A); DROP; NIP; AX(i;i,0,0);
                  NIP^9; DROP; NIP; NIP
    MP to B: Build(A); DROP; Build(I(A,B)); NIP; DROP; NIP;
             MP(B); AX(B;0,0,0); NIP^10; DROP; NIP; NIP.

All eight rows and every bundle have outer tag zero, and GEN has tag two, so none equals target 1. The cleanup AX gates fail because `c=a`. These tag facts, pair inverse equations, and the unchanged count of ten pushed values prove each block contract directly. The shifted pairing changes the actual numbers but none of those equations. Induction on a `C_p` proof constructs the block.

Given `Build(F)`, prepend `AX(0;1,1,u)` and append `DROP;NIP;NIP`. The leading AX resets `d=h=0` from every working state; its current formula and stack may be arbitrary, exactly as permitted by the build contract. The final three commands halt if the build has not halted sooner. The padded candidate number is

    p(3,p(1,p(1,p(u,r))))

where `r` includes the next-command successor delimiter. It is at least `u` by the field bounds. Choose `u≥initial np`. Candidate draining and successive counter increments ensure that this candidate is eventually reached, unless an earlier genuine halt occurs. Thus no refutation is lost by starting at candidate 3 or by a nonzero additive parameter. Completeness in fact holds from every six-register state; soundness requires the invariant.

The nine logical source registers have order `(N,T,W,A,D,H,X,Y,L)`. Its requested seed maps to

    (pl,np,t,S,d,h)=(0,3,0,0,3,0), with A=X=Y=0.

All three formula-bearing fields are zero, so the invariant holds. The two nonzero fields are control/parameter data. Therefore

    Halt(Enum_E, seed) iff C_E(1) iff Ref(NativeAx).

The original source's ordinary NativeAx/SIR-to-ZFC comparison is unchanged. It includes the actual set-coded interpretation, internal Foundation and constructible Choice argument; it is not replaced by external well-foundedness or a schema over arbitrary semantic relations. Composing that inherited comparison gives the ordinary assertion

    ZFC proves: Halt(Enum_E,seed) iff exists q Prf_ZFC(q,bottom).

Taking classical negations gives the desired nonhalting/Con(ZFC) equivalence at the **abstract changed enumerator** level.

## 7. Source and literal binary-machine obligations

For the direct helper replacement proposed by the companion source-design lane, sufficient clean contracts are:

- Pair: entry `X=a,T=b,Y=0`; return `X=T=0,Y=E(a,b)`; preserve every other register
- Unpair from `L` or `W`: entry `source=n,X=Y=0`; return `source=0,X=u(n).1,Y=u(n).2`; preserve every other register
- Finite return at the correct continuation for every such entry, with no unintended halt

The identities in Section 1 prove the arithmetic loop invariants for clean inputs. They do not prove that a particular nested decrement/break/continue AST implements those loops or that every call is clean. The old Cantor inverse contract on arbitrary scratch was `u_Cantor(P_Cantor(X,Y)+source)`. A clean shifted inverse need not satisfy an analogous dirty contract; no such claim is made. The source proof may instead establish the needed scratch-zero invariants from the exact seed and at every helper call, then compose the existing higher-level constructors with the new clean contracts. Each scalar push, binary formula constructor, stack operation, field read, comparison, gate, and command must then have the Section 5 meaning with `E`.

The companion source-design lane subsequently supplied `../shifted-clean-entry-audit.json` and `../best-clean-entry-audit.json`: each records an inductive zero/nonzero overapproximation over 625868 abstract states of the 7788-leaf changed source, with clean X,Y at external unpair entries and clean Y at external pair entries. `../shifted-source-results.json` records the original and changed source measurements and helper tests. Those finite certificates address the call-entry concern; they are separate work, not a kernel proof or an exact-table simulation. The companion reports a directly hash-consed source DAG increase from 219 to 234 nodes, reduced to 232 across 200 local shapes. These are source-DAG measurements, **not** binary-machine state counts or a lower bound on other implementations.

For an emitted literal binary table `M_E`, one additionally needs:

1. A count of its actual nonhalting states and an exact canonical table
2. A complete-frame simulation for the *new* source, for every reachable legal register frame and continuation, with finite positive clocks in both halting directions
3. A verified exact blank-tape run reaching a safe frame with the displayed logical seed, or another seed satisfying the theorem's invariant; a changed grammar need not keep the old 407915-step bootstrap
4. Any altered runtime allocation/routing bounds, header, tape exterior, pointer stack, and spare suffix requirements checked for that exact table

Only then follows `ZFC proves: not Halt_blank(M_E) iff Con(ZFC)`. No old/new numerical-register equality bisimulation is expected, and no old table certificate is transferred merely because the source's abstract logic is equiconsistent.

## 8. Checks and provenance

`check_shifted_pairing.py` is independently authored mathematical test code and imports no downloaded project code. Its recorded run checks inverse/field/decoder-label facts for all 65536 integers below 2^16, 32800 encoder/inverse cases, and 17152 exact command-pack round trips. It also verifies the concrete direct-gate-recoding counterexample. These finite checks supplement the proofs above, not a replacement for them. No supplied Lean, Python, or other downloaded source was executed, imported, or compiled.

The source definitions read as data include the packaged `Code254.lean`, `Code254Proof.lean`, `Enum254.lean`, `EnumSafeStart254.lean`, and `L2Lib254.lean`, plus the source-search packet's exact normalized-calculus transfer. The additional native adapters were retrieved as text at ProveIt commit `fd1adfa19f8fe8da41444e3fa43b89a59d891067` and preserved under `sources/` with `.txt` suffixes:

- [Code254GIC.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/fd1adfa19f8fe8da41444e3fa43b89a59d891067/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254GIC.lean): positive encoding, occurring-label bounds, padding, exact bundle encoding, hygienic native matrix adapter
- [Code254Containers.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/fd1adfa19f8fe8da41444e3fa43b89a59d891067/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254Containers.lean): exact C/G/bundle trees and fixed container instance
- [DecodeFresh254.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/fd1adfa19f8fe8da41444e3fa43b89a59d891067/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DecodeFresh254.lean): the positive decoder support bound and semantic code-zero exception
- [NativeDecoded254.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/fd1adfa19f8fe8da41444e3fa43b89a59d891067/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NativeDecoded254.lean): both native-model adapters, full equality-inclusive GIC, and the a=b case
- [Code254Models.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/fd1adfa19f8fe8da41444e3fa43b89a59d891067/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254Models.lean): exact decoded/encodable model predicates and semantic round trip
- [NativeTheory254.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/fd1adfa19f8fe8da41444e3fa43b89a59d891067/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NativeTheory254.lean): unchanged NativeAx and ordinary refutation interface

The report's genericization and shifted-pairing transfer are new mathematical work here. The compact calculus and set theory are inherited from Mira-Cult, the original verification from Jeff Ketchersid, the compiler from Andrew James Wade, and the inspected native adapters from ProveIt. This attribution does not assert a new formal build of any inherited or changed endpoint.
