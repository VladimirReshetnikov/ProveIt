# Curated exact source excerpts

These are source lines, not new proposals. Full source receipts and immutable repository URLs are supplied separately. Ellipses are not inserted inside excerpts.

## zh finite rigidity

Original source: `03-physical.tex`, lines 1–29; full-source Git blob `cf9dcae3657be131479e87df37632f4489c32623`, SHA-256 `8b77eb3c5a61f7ca03eacaa9c05820c47af06a9408f921cafe26db24a0fbd2e6`.

```text
1: \pageheading{3 Reuse rigidity of a finite ordinal}
2: \textbf{Target.} \src{WangTiles942PhysicalOrder}{68}{97} proves that a strictly increasing self-map of \(\operatorname{Fin}(n)\) fixes every point. The current proof obtains surjectivity, performs strong induction on the numerical index and splits the preimage into three cases. The exact conclusion follows from the existing rigidity theorem for finite order isomorphisms.
3: 
4: \textbf{Mathematical proof.} A strictly monotone map \(f\) is injective. Since domain and codomain are the same finite set, it is surjective. Strict monotonicity on a linear order gives \(f(i)\le f(j)\iff i\le j\), so this bijection is an order isomorphism. An order isomorphism takes the strict lower segment of \(i\) bijectively onto the strict lower segment of \(f(i)\). These segments have respectively \(i\) and \(f(i)\) elements, hence their values are equal. Extensionality in \(\operatorname{Fin}(n)\) finishes. The empty case is vacuous and no positivity hypothesis on \(n\) is needed.
5: 
6: \textbf{Exact replacement sketch.} All order-isomorphism packaging is included:
7: \begin{lstlisting}
8: theorem strictMono_fin_eq_self {n : ℕ} (f : Fin n → Fin n)
9:     (hf : StrictMono f) (i : Fin n) : f i = i := by
10:   let e : Fin n ≃o Fin n :=
11:     ⟨Equiv.ofBijective f
12:       ⟨hf.injective, Finite.surjective_of_injective hf.injective⟩,
13:       hf.le_iff_le⟩
14:   exact Fin.ext (Fin.coe_orderIso_apply e i)
15: \end{lstlisting}
16: The shipped candidate uses the same proof with the original declaration header; its declaration is 30 to 6 physical lines and its body 28 to 4. The whole file is 180 to 156. The wrapping above is for page readability, not the measurement. No helper, import or downstream edit is added. In particular, \code{rankMap_eq}, physical positions and the Start convention are unchanged.
17: 
18: \textbf{Pinned library support.} \href{https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Order/Fin/Basic.lean\#L394-L399}{Mathlib \code{Order/Fin/Basic.lean}:394--399} contains \code{Fin.coe_orderIso_apply}. Its module is already supplied by the physical-data import. This is exact client reuse, not a proposed new general rigidity lemma. The nearest older ideas are packet i's finite invariant-set surjectivity, packet k's exploratory order embeddings and packet s's prefix-rank/cardinality reasoning. None removes this new explicit induction.
19: 
20: \textbf{Optional definition edit.} At source lines 41--52, use the standard predecessor:
21: \begin{lstlisting}
22: def nonStartIndex (j : Fin 941) : Fin 941 :=
23:   (abstractIndex j).pred (abstractIndex_ne_zero j)
24: 
25: theorem nonStartIndex_succ (j : Fin 941) :
26:     (nonStartIndex j).succ = abstractIndex j :=
27:   Fin.succ_pred (abstractIndex j) (abstractIndex_ne_zero j)
28: \end{lstlisting}
29: This saves another seven physical lines, yielding 149 combined. It changes a definition body, so it is separately selectable. Pinned Lean 4.32.0 defines \code{Fin.pred} by subtracting one; the nonzero proof and protected Start remain. A prepared \code{rfl} regression compares it with the old constructor, but has not been compiled. Test the proof-only variant first; if both are adopted use the supplied combined patch, not two overlapping whole-file alternatives.
```

## zj finite rigidity

Original source: `report.tex`, lines 82–114; full-source Git blob `c204e3674551bd5ee55c040f0427c2cba3e7ab18`, SHA-256 `3a0c37d536c3aa16522925efee423b1c08a076eef96818596832402a1428b5bb`.

```text
82: \section{P1: finite-order rigidity replaces strong induction}
83: \label{sec:order}
84: 
85: \textbf{Target.} \repo{Lean/DiophantineConsistency/WangTiles942PhysicalOrder.lean}{\code{WangTiles942PhysicalOrder.strictMono_fin_eq_self}}.
86: 
87: The maintained proof establishes that a strictly increasing self-map of \code{Fin n} fixes every element. It first turns injectivity into surjectivity, then performs strong induction on the underlying natural index. At each index it obtains a preimage and compares that preimage with the index, splitting into smaller, equal and larger cases. This is a complete proof of a fact already packaged in the pinned library.
88: 
89: For any finite linearly ordered type $A$, an injective monotone map $f:A\to A$ is the identity. Mathlib provides this as \ml{Data/Finset/Sort.lean}{\code{OrderHom.eq_id_of_injective}}. Strict monotonicity supplies both required facts. Equality of the bundled maps can then be evaluated at the desired element:
90: 
91: \begin{Lean}
92: theorem strictMono_fin_eq_self {n : ℕ} (f : Fin n → Fin n)
93:     (hf : StrictMono f) (i : Fin n) : f i = i := by
94:   exact DFunLike.congr_fun
95:     (OrderHom.eq_id_of_injective
96:       (⟨f, hf.monotone⟩ : Fin n →o Fin n) hf.injective) i
97: \end{Lean}
98: 
99: The production patch fits the final application on one line and retains the original declaration header. The old declaration occupies 30 physical lines; the replacement occupies four. One direct import of \code{Mathlib.Data.Finset.Sort} makes the dependency explicit, leaving a net saving of 25 lines in the complete module.
100: 
101: \subsection*{Why the mathematics fits exactly}
102: 
103: Injectivity on a finite set gives surjectivity. A finite chain has no nontrivial order automorphism: its least element must be fixed, then the least remaining element must be fixed, and so on. The source proof reconstructs this argument; the library theorem packages it. No assumption $n>0$ is needed. For $n=0$ there is no element to prove fixed, while the singleton case follows automatically.
104: 
105: The standalone file also checks the same statement for an arbitrary finite linear order. Linearity matters. A finite partial order with two incomparable elements admits their exchange as an order automorphism, so replacing the linear-order condition with a partial-order condition would be false.
106: 
107: \subsection*{Effect on the physical-order proof}
108: 
109: The client \code{rankMap_eq} still obtains strict monotonicity from \code{rankMap_strictMono}. That theorem still depends on the actual descending weights and strict-rank facts. The replacement removes only the generic rigidity argument; it does not certify the numerical physical-order table or eliminate its coverage and ordering obligations.
110: 
111: The original and replacement standalone declarations both compiled, and both report precisely \code{propext}, \code{Classical.choice} and \code{Quot.sound}. An independent reviewer also compiled the replacement and checked the empty and singleton cases. No compilation-speed or compiled-object reduction is inferred from the shorter text.
112: 
113: \textbf{Novelty boundary.} Earlier proposals cover finite predecessor invariance, positive-tail physical-position injectivity, and construction of internal order from a strict relation. The audit found no proposal for this finite-chain endomorphism rigidity deletion in the newly added physical-order module. The contribution is this library reuse at the exact target, not a new order-theoretic theorem.
114: 
```

## zd exact numerical order certificates

Original source: `report.tex`, lines 255–373; full-source Git blob `a7217dbdb4ac0629a6743a8254234d48eaabd263`, SHA-256 `048fe4f49d29b1583dae104282dee70c74652ecccb20a867a134282f3863b19c`.

```text
255: \section{Replace prime-divisor case trees with finite order certificates}
256: 
257: \subsection{The mathematical criterion already exists}
258: 
259: The source
260: \repo{CurrentControllerData2011}{\name{CurrentControllerData2011.lean}}
261: proves that 2 has order 23 modulo 47 and order 402 modulo 2011. It already
262: uses Mathlib's \name{orderOf_eq_of_pow_and_pow_div_prime}. The cumbersome
263: part is the proof that a prime dividing 402 must be one of 2, 3, or 67.
264: The current source repeatedly splits divisibility of products and converts
265: prime divisibility into equality.
266: 
267: For an element \(x\) of a monoid, a positive candidate order \(n\) is exact if
268: \[
269:  x^n=1,\qquad
270:  \forall p\in\operatorname{primeFactors}(n),\quad x^{n/p}\ne1.
271: \]
272: The mathematical reason is that \(x^n=1\) makes the actual order divide
273: \(n\). If the actual order were a proper divisor, some prime divisor of the
274: quotient would yield a smaller exponent \(n/p\) at which \(x\) is already 1.
275: Mathlib supplies the criterion; this proposal changes the finite interface
276: for its remaining premise.
277: 
278: The exact membership theorem in the pinned Mathlib version is
279: \[
280:  p\in n.\name{primeFactors}\quad\longleftrightarrow\quad
281:  \operatorname{Prime}(p)\land p\mid n\land n\ne0.
282: \]
283: Thus the finite certificate is complete, not just a list of convenient tests.
284: This distinction matters: listing a few proper powers without proving that
285: the list contains every relevant prime divisor would not establish the order.
286: 
287: \subsection{A small adapter with an accounted cost}
288: 
289: The candidate adds \name{Mathlib.Data.Nat.PrimeFin} and one private theorem:
290: 
291: \begin{lstlisting}
292: private theorem order_eq_of_factors {M : Type*} [Monoid M] (x : M) {n : ℕ}
293:     (hn : 0 < n) (hpow : x^n = 1)
294:     (hproper : ∀ p ∈ n.primeFactors, x^(n/p) ≠ 1) : orderOf x = n := by
295:   apply orderOf_eq_of_pow_and_pow_div_prime hn hpow
296:   intro p hp hpn
297:   exact hproper p (Nat.mem_primeFactors.mpr ⟨hp,hpn,Nat.ne_of_gt hn⟩)
298: \end{lstlisting}
299: 
300: The two public clients then reuse their existing power-equals-one facts:
301: 
302: \begin{lstlisting}
303: theorem two_order_47 : orderOf (2 : ZMod 47) = 23 :=
304:   order_eq_of_factors _ (by decide) two_pow_47 (by decide)
305: 
306: theorem two_order_2011 : orderOf (2 : ZMod 2011) = 402 :=
307:   order_eq_of_factors _ (by decide) two_pow_2011 (by decide)
308: \end{lstlisting}
309: 
310: The final calls use ordinary \name{decide} on closed finite propositions.
311: Their concrete Mathlib elaboration and reduction cost still need to be
312: measured. An earlier
313: prototype that explicitly rewrote each prime-factor set and then split its
314: members did not repay the helper cost as well. The delivered patch uses the
315: closed certificate directly and includes its full cost in the measurement.
316: 
317: The complete module changes from 184 to 178 physical lines: 18 deleted and
318: 12 added, including the import and the six-line private theorem. Existing
319: named proper-power residues remain in the module, as do the order facts for
320: the large base, the auxiliary lift, and the conditional kernel-residue wrappers.
321: There is no new claim that the actual kernel residues have been discharged.
322: 
323: \subsection{Guards and edge cases}
324: 
325: The premise \(n>0\) must remain. At \(n=0\), the prime-factor set is empty and
326: \(x^0=1\) holds automatically. Removing the positivity guard would therefore
327: turn an empty finite check into a false general order assertion. At \(n=1\),
328: the prime-factor check is correctly empty: \(x^1=1\) itself proves that the
329: order is one.
330: 
331: No primality of the ambient modulus is used by the adapter. The finite tests
332: concern prime divisors of the \emph{candidate order}, not the modulus. This is
333: why the adapter is stated for a monoid, with no finite-group instance. The two
334: particular moduli happen to be prime, but that fact is not smuggled into the
335: criterion as an unnecessary assumption.
336: 
337: The nearest prior finite-certificate proposals concern tile tables, chunks,
338: coefficient fibres, or decoder bounds. This candidate concerns the completeness
339: of the exact-order test family. It is a new local application of an existing
340: order theorem, with a small measured payoff, not a new certificate engine.
341: 
342: \subsection{Independent kernel evidence for the concrete numbers}
343: 
344: The supplied \name{FiniteOrderCore.lean} uses a small recursive evaluator that
345: reduces modulo \(m\) after each multiplication:
346: \[
347:  r_0=1\bmod m,\qquad r_{k+1}=r_k b\bmod m.
348: \]
349: It proves \(r_k=b^k\bmod m\) for every \(b,m,k\), then checks the positive
350: return time and \emph{every} smaller positive exponent for the two candidates.
351: Consequently it establishes the ordinary arithmetic statements
352: \[
353:  \begin{aligned}
354:  2^{23}&\equiv1\pmod{47}, &
355:  0<k<23&\Longrightarrow 2^k\not\equiv1\pmod{47},\\
356:  2^{402}&\equiv1\pmod{2011}, &
357:  0<k<402&\Longrightarrow 2^k\not\equiv1\pmod{2011}.
358:  \end{aligned}
359: \]
360: It also checks the three residues relevant to the smaller factor certificate:
361: \[
362: 2^{201}\bmod2011=2010,\quad
363: 2^{134}\bmod2011=205,\quad
364: 2^6\bmod2011=64.
365: \]
366: 
367: The finite certificate declarations and the three residue computations have
368: empty axiom sets. The evaluator correctness and the resulting ordinary
369: first-return theorems use only \name{propext}. This evidence rules out an
370: incorrect numerical order or missing smaller return. It does \emph{not}
371: certify the imported \name{primeFactors} adapter, its typeclass elaboration,
372: or the proposed production \name{decide} calls. Those remain a distinct gate.
373: 
```

## zh controller nondivisibility

Original source: `04-controller.tex`, lines 1–22; full-source Git blob `fdf54acb6d2a356da79b26f07489b85a9c3a28fc`, SHA-256 `69a84e5757f03107c146b42ad3684c9b0d60caa636130251d2024e02d6f615f5`.

```text
1: \pageheading{4 Use the direct divisibility criterion for cardinality}
2: \textbf{Target.} \src{ControllerAuxiliaryChoice}{26}{48} constructs a Boolean choice and a positive cardinality coprime to every power of the auxiliary prime. Its mathematical argument is already correct and its witness already explicit. The residual duplication is a hand-built bridge from nonzero reduction modulo the prime to nondivisibility of the least natural representative.
3: 
4: \textbf{Mathematical proof.} Let \(p\) be prime with \(p\mid C\), and let \(\phi:\Z/C\to\Z/p\) be the reduction homomorphism. Suppose \(\phi(b)\ne0\). At least one of \(\phi(t)\) and \(\phi(t-b)\) is nonzero: otherwise subtracting gives \(\phi(b)=0\). The existing Boolean-choice theorem therefore supplies \(e\in\{0,1\}\) such that, for \(r=t-eb\), \(\phi(r)\ne0\).
5: 
6: Set \(a=r.\mathrm{val}\). The standard cast identity identifies \((a:\Z/p)\) with \(\phi(r)\). By \((a:\Z/p)=0\iff p\mid a\), we obtain \(p\nmid a\). If \(a=0\), then \(p\mid a\), a contradiction; hence \(0<a\). The canonical representative also satisfies \(a<C\), while its cast in \(\Z/C\) is exactly \(r\). Finally, primality gives \(\gcd(a,p^n)=1\) for every \(n\), including \(n=0\). Every witness and endpoint in the old theorem is retained.
7: 
8: \textbf{Exact replacement sketch.} After the existing derivation of \code{hr}, the fact that \(\phi(r)\ne0\), replace the local cast equality and contradiction chain with:
9: \begin{lstlisting}
10:   have hnd : ¬ p ∣ r.val := by
11:     rw [← ZMod.natCast_eq_zero_iff, ZMod.natCast_val]
12:     exact hr
13:   have hpos : 0 < r.val :=
14:     Nat.pos_of_ne_zero fun hz => hnd (hz ▸ dvd_zero p)
15: \end{lstlisting}
16: Keep the original final tuple, including \code{hp.coprime_pow_of_not_dvd hnd}. The public declaration drops from 22 to 16 lines, and the whole file from 50 to 44. No helper or import is added. This is six lines of specific new-client reuse, not a new modular-arithmetic abstraction or a solution of the remaining power-orbit and safe-position obligations.
17: 
18: \textbf{Pinned support and elaboration risk.} \href{https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Data/ZMod/Basic.lean}{Mathlib \code{Data/ZMod/Basic.lean}} supplies \code{natCast_val} at line 263 and \code{natCast_eq_zero_iff} at line 518. Their exact statements are retained in the API receipt. Lean still needs to confirm type inference and the definitional match between \code{cast} and the local \code{phi}. If that reduction needs an explicit \code{change} or \code{simpa}, include its cost rather than silently preserving the advertised six-line saving.
19: 
20: \textbf{A nearby proposal was withdrawn, not repackaged.} An initial screen suggested shortening \code{ControllerResidueLift.exists_coordinate} with \code{castHom_apply}, \code{cast_eq_val} and \code{val_natCast}. A closer baseline check found that exact chain in \prior{p}{lean/DiophantineConsistency/SupportDifference.lean}{27}, lines 27--34, already proposed as \code{residue_val}. Under the assumed-applied rule this is old infrastructure, even at a fresh client. The five-line projection patch was removed from the retained artifacts and all totals.
21: 
22: The nearest broader precedents for the surviving cardinality edit are E17 residue interfaces and LE24 cast normalization. They establish the approach, but not this exact nondivisibility-to-positive-coprime-witness deletion. The report credits only that residual client cost. This withdrawal is why a final accounting pass must follow semantic comparison, rather than treating an initial keyword screen as a novelty proof.
```

## prior Sidon moment-only proposal

Original source: `report.tex`, lines 524–538; full-source Git blob `f97edf98a4dc2870e3fef8ca418cc7b663e03cd4`, SHA-256 `c0d2ee1579676dcde451a64991cd313b640f96821f4ec82b78c97fd56b85e3a8`.

```text
524: \section{Supplement: direct polarization in the Sidon argument}
525: 
526: The archive also includes a smaller independently checked edit to \source{SidonPositions}. It is deliberately not counted as an eighth mathematical direction. The source already uses the familiar sum-and-sum-of-squares argument to recover an unordered pair; the new edit changes the route through the polynomial identity, rather than introducing that mathematical fact.
527: 
528: After moving the relevant equalities to integers, use the identity
529: \[
530: 2(a-c)(a-d)
531: = (a^2+b^2-c^2-d^2)
532: +(a-b-c-d)(a+b-c-d).
533: \]
534: If the first two moments agree, both terms on the right vanish. The resulting zero product yields $a=c$ or $a=d$, and the sum equation recovers the other coordinate. A deterministic \code{linear_combination} step avoids separately deriving the intermediate equality of products.
535: 
536: The particular identity is the proposed delta. Generic cast normalization with \code{zify}, polynomial normalization, and the original factorization argument are not claimed as new ideas. This narrow framing matters because earlier packets already discuss cast cleanup, coefficient fibres, and the existing Sidon interface.
537: 
538: The exact theorem declaration changes from 26 to 17 physical lines; the full candidate module changes from 168 to 161 lines after charging two explicit imports. Both the isolated theorem check and the complete modified \code{SidonPositions.lean} module completed successfully against the pinned dependencies. The logs and full-module receipt are supplied under \code{arithmetic/evidence}. This additional full-module check does not imply that the other production patches were built.
```

## prior metadata relocation

Original source: `report.tex`, lines 269–282; full-source Git blob `742067eba3cbf521cc4a26724055cd219d6df69c`, SHA-256 `9c606a8955fcd2ceb15c462ff30bc4e265f7a60a09eaa3b278f1b566dde58fdb`.

```text
269: \subsection{Move existing projection lemmas to their natural home}
270: 
271: The desired witness-count simplification lemmas already exist in
272: \src{RepresentationSize}{136--147}, with graph analogues at lines
273: 193--209. However, \src{DirectComposition}{59--68} still unfolds whole
274: constructors to compute counts. It cannot import the size module without
275: reversing the present dependency direction.
276: 
277: Move the small \code{rfl} projection lemmas next to the constructors or
278: into a lightweight module that imports only the constructors. The size
279: module can then concentrate on global bounds. This changes which facts
280: are available early, rather than adding duplicate facts. It also prevents
281: the simplifier from examining large expression and proof fields merely
282: to calculate a natural-number projection.
```
