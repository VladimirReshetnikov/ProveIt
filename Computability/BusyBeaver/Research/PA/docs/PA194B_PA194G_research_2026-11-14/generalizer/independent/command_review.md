# Independent command review of PA194G

## Verdict and scope

The proposed command change is mathematically sound **provided the independently checked source binding has exactly the interface below**. The changed generalization head is `U(c,h)`, using the explicit first AX operand and the incoming cached formula. It is not `U(c,H)` with `H=h+y`. This review checks the command algebra and proof compiler; the construction agent supplies literal source, decoder, physical-outcome and initialization evidence.

The shortened generalization word is correct, including when the input formula is numerical contradiction code one. The appropriate Pop lemma for this machine is **total**, because its Shift uses the original sum guard. The cache-only H-family Pop lemma would be wrong here.

## Exact interface

Let `P` be Cantor pairing, `[a;w]=P(a,w)`, and use its total projections `hd`, `tl`. In particular `[0;0]=0` and `hd(0)=tl(0)=0`. A store is `(t,w,d,h)`. Set

\[
I(A,B)=4P(A,B),\qquad U(i,A)=4P(A,i)+2.
\]

The commands are

\[
S(t,w,d,h)=
\begin{cases}
\mathsf{halt},&t+h=1,\\
(h,\operatorname{tl}(w),d,\operatorname{hd}(w)),&t+h\ne1;
\end{cases}
\]

and, with `v=d+x`,

\[
MP_x(t,w,d,h)=
\begin{cases}(v,w,v,0),&I(t,v)=h,\\(0,w,v,0),&I(t,v)\ne h.
\end{cases}
\]

For `D=d+x`, `H=h+y`, the changed command is

\[
AX_{c,x,y}(t,w,d,h)
 =\bigl(g(H,D,c),[q_1,\ldots,q_9,t;w],0,0\bigr),
\]

with

\[
(q_1,\ldots,q_9)
=(\Gamma(c),h_6^Q(D,c,H),h_5(D,H),h_4(D,c,H),h_3(D,c,H),
h_2(D,c,H),h_1(D,H),\rho(D,c,H,d),U(c,h)).
\]

The guarded gate and `q1` through `q8` are zero modulo four; `q9` is two modulo four and at least two. The numerical constructors need not form free syntax at zero for these facts to hold.

## Uniform stack lemmas

Write `A0=AX_{0,0,0}`, and execute words from left to right. Direct induction through the Shift iterations gives

\[
AX_{c,x,y};S^9(t,w,d,h)
 =(\rho(D,c,H,d),[t;w],0,U(c,h)),
\]

\[
AX_{c,x,y};S^{10}(t,w,d,h)
 =(U(c,h),w,0,t).
\]

Neither word halts. Every tested sum before the last generated head is a sum of two multiples of four, or a multiple of four plus a number congruent to two; neither can be one. The arbitrary saved top has not yet been tested against another arbitrary value.

Consequently

\[
Push=A0;S^9;MP_0
\]

is total on arbitrary stores and sends `(t,w,d,h)` to `(0,[t;w],0,0)`. The MP necessarily takes its failed comparison branch because its implication code has residue zero while the cached `U(0,h)` has residue two.

For

\[
Pop=A0;S^{11},
\]

the tenth Shift leaves `(U(0,h),w,0,t)`. The eleventh guard tests `U(0,h)+t`, which is at least two. Thus Pop is total and

\[
Pop(t,w,d,h)
=(t,\operatorname{tl}(w),0,\operatorname{hd}(w)).
\]

In particular `Pop(t,[a;w],d,h)=(t,w,0,a)` for every natural `t,a,d,h,w`, including the numerical zero-stack alias. A final Pop does **not** by itself detect a returned contradiction in this sum-guard protocol.

Finally `Discard=MP_0`, on any store with `d=0`, sends `(t,w,0,h)` to `(0,w,0,0)`: both MP branches have consequent zero and identical resulting stores.

## Shortened generalization compiler

The proposed word is

\[
Gen_i=Push;S;AX_{i,0,0};S^{10}.
\]

Its important boundary stores are

\[
(a,w,0,0)
\xrightarrow{Push}(0,[a;w],0,0)
\xrightarrow{S}(0,w,0,a)
\xrightarrow{AX_{i,0,0};S^{10}}(U(i,a),w,0,0).
\]

The isolated Shift tests `0+0`, not `a`; when `a=1`, AX consumes the cached contradiction before another Shift can test it. The subsequent nine generated zero-residue heads and the residue-two generalization head satisfy the safe-sum argument above. Hence the word is total and the advertised identity includes `a=1`. The old `Offset_i=MP_i` is genuinely unnecessary because the quantifier label is now supplied directly by AX's operand `c=i`. In fact Push clears arbitrary incoming `d,h`, so the same conclusion holds starting from `(a,w,d,h)`.

## Axiom selectors and MP composition

The old no-push selectors retain their indices: the stack still has exactly ten pushed entries, including the saved top. For `1<=j<=7`, from an arbitrary `(t,w,0,0)`,

\[
Discard;AX_{A,D,H};S^{j+1};Pop^{9-j}
\]

returns `(q_j,w,0,0)`. The gate selector is `Discard;AX_{c,b,a};Pop^10`. For `u<=a`, the dominated-head selector is

\[
Discard;MP_u;AX_{b,a-u,c};S^9;Pop.
\]

It returns `(rho(a,b,c,u),w,0,0)`. The changed ninth head only supplies the safe residue-two temporary cache; it does not change the selected rho or its condition `u<=a`.

The MP suffix remains `S;S;MP_b;Pop`. From `(0,[a,I(a,b),0;w],0,0)`, it halts early if `a=1`, and otherwise returns `(b,w,0,0)`, including `b=1`. A zero was reserved so that the final Pop does not consume the arbitrary older stack. At an MP node, the word

\[
Discard;Push;W_{\rm major};Push;W_{\rm minor};Push;S;S;MP_b;Pop
\]

has the required invariant: either halt or return the node's conclusion while preserving the arbitrary older stack and clearing both bookkeeping fields. The first Discard/Push reserves the zero. Induction over proof trees, using the new Gen word, therefore supplies `W_p` with this invariant.

If `p` concludes one, the all-store refutation word is

\[
A0;W_p;S.
\]

Initial AX clears `d,h`; `W_p` either already halts or returns `(1,w',0,0)`; final Shift then tests `1+0=1`. The compiler needs this final **Shift**, not the H-family final-Pop detector. The AX field count and command-word encoder remain the ordinary three-operand versions, unlike the prior AX11 protocol.

## Soundness and PA proof transport

Annotate visible top, cache, and canonical live stack entries with numerical-calculus proofs. The new head `U(c,h)` is obtained by theorem generalization from the cached proof of `h`, for any natural label `c`. There is no assumption to discharge and no side condition connecting `c` with the offset `d`. All other emitted axioms and the numerical dominance condition `d<=D` remain unchanged. MP preserves proof annotations; Shift only halts when one of its two theorem codes is one. Thus the change introduces no additional axiom and removes no necessary inference rule.

The explicit selectors, shortened Gen compiler, framed MP suffix, and all-store refutation word show completeness for the same Q calculus. Their finite proof/word transformations are primitive recursive and their algebraic identities are PA-verifiable. Composing these with the supplied Q-calculus PA calibration and the separately verified source/tape simulation gives the intended ordinary PA consistency equivalence. This review does not claim a newly kernel-checked end-to-end theorem.

## Structural and naming review

The dense table SHA-256 is `28bd991a84200351f36c98afac369ab5a555eb8793821ad35555f0aa4a0fdeeb`. Exact canonical comparison finds no match among all 82 prior 194-state graphs, even with state renaming, every spanning root, reflection, bit exchange and ignored terminal-edge actions. PA194G has 21 self-loops and is also distinct from the separately constructed PA194B, which has 22. No whole-word PA194G name was found in the filed or incoming report texts. The corpus contains general proposals to change quantifier indices and related source searches; novelty should be stated as this concrete checked explicit-operand generalization protocol and literal realization, not as discovery of generalization with arbitrary variable labels.
