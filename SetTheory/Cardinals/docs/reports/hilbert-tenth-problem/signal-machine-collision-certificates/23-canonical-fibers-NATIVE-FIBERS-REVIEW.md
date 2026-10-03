# Independent review: fixed-scale native witness fibers

**Verdict: PASS.** Every nonempty positive-witness fiber of the prescribed native AND64 block is infinite, with the external ports and scale fixed. The proposed seed-unit construction is correct; the fixed-matrix construction below is slightly simpler. The only necessary wording correction is that computed gate values can change: it is the other **witness coordinates**, and the other **comparison truth values**, that remain fixed.

## 1. Exact source audit

I independently read the literal arithmetic JSON, without executing any repository Python:

- Input: `../inherited-source/three_mass_unbounded_interface.json`
- SHA-256: `fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e`
- Its adjacent provenance file identifies commit `ad634b2d10ad666260f9fdff04ec94b75169ee4b` and Git blob `766cd6c6eaa9e46cdff58ba9650d4a72caf47f00`.
- Each of its four fixtures (`incdec`, `zero3`, `nop`, `positive3`) has exactly 64 native gate rows, 22 native positive witness coordinates, and 16 native comparisons. Native rows after the first seven port-adapter rows are identical across all four fixtures.

I also retrieved and read the [pinned binary-selector proof, sections 1–2](https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_binary_selector56.md) using a read-only raw-file request. Its ten core equations agree with the local literal native block. In particular, writing

\[
p=2r+1,\quad R=ic^2,\quad U=jc-p,
\]

the relevant two equations are exactly

\[
R^2(U^2-y_{\rm aux}^2)=1-y_{\rm aux}^2,\qquad U=of-c.
\]

The audit found direct occurrences of the three varied witnesses only in native gate rows 54 (`of=o*f`), 56 (`jc=j*c`), and 59 (`aux_y2=y_aux*y_aux`), numbering native gate rows from 1. Their only dependent native comparison pairs are:

1. Native comparison 13: `L17=P17`, the displayed auxiliary norm equation.
2. Native comparison 14: `H17=aux_u_rhs`, the displayed linear congruence equation.

The dependent native gate outputs are exactly `of`, `aux_u_rhs`, `jc`, `H17`, `H2`, `aux_y2`, `aux_square_gap`, `L17`, and `P17`. The full emitted circuits subsequently use these only through the two corresponding SOS residuals and their downstream SOS arithmetic. Those residuals remain zero. There is no hidden comparison, positivity requirement on a signed intermediate, or port dependence that constrains the proposed family.

The 22 positive coordinates are `F0,F1,F2,a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y_aux,odd_half,bound_beta`. Thus fixing all but `j,o,y_aux` fixes 19 coordinates.

## 2. Positivity hypotheses are available without the deep Pell classification

The prescribed block has positive scale \(\nu\), with \(q=16\nu\), and positive `odd_half`, with \(s=2\,\mathrm{odd\_half}+1\). Its equations include

\[
k=r+1+hE,\qquad c=(sq)k+\eta,
\]

where all quantities on the right are positive. In particular, \(sq\ge48\), \(k>r+1\), and \(c>2r+1=p\). Since \(j\ge1\), the seed satisfies \(U=jc-p>0\). Also \(R=ic^2>1\), \(y_{\rm aux}>0\), and \(f>0\). These deductions also follow from the cited source, but do not require its deeper index or parity conclusions.

## 3. Verified fixed-matrix construction

Take any positive seed in a fixed-port, fixed-scale fiber. Put

\[
D=R^2-1>0,\qquad V_0=RU,\quad Y_0=y_{\rm aux},\qquad
B=\begin{pmatrix}R&D\\1&R\end{pmatrix},\qquad N=Rcf.
\]

The source norm is equivalent to

\[
V_0^2-DY_0^2=1.
\]

Both entries of the seed vector are positive integers. The matrix has strictly positive integer entries and determinant \(R^2-D=1\). Therefore its reduction modulo \(N\) is invertible and has a finite positive order \(L\). An explicit valid, though unnecessarily large, choice is \(L=(N^4)!\): there are at most \(N^4\) residue matrices, so the order is an integer at most \(N^4\), and hence divides this factorial. No claim that the order divides \(N^4\) is needed.

For every integer \(n\ge0\), define

\[
\binom{V_n}{Y_n}=B^{nL}\binom{V_0}{Y_0}.
\]

The following checks are exact:

- **Norm:** For any \(V,Y\),
  \[
  (RV+DY)^2-D(V+RY)^2=(R^2-D)(V^2-DY^2)=V^2-DY^2.
  \]
  Hence \(V_n^2-DY_n^2=1\).
- **Congruence:** \(B^{nL}\equiv I\pmod N\) gives \(V_n\equiv V_0=RU\pmod{Rcf}\). Thus \(U_n=V_n/R\) is an integer and \(U_n\equiv U\pmod{cf}\).
- **Reconstruction:** Set
  \[
  j_n=(U_n+p)/c,\qquad o_n=(U_n+c)/f,\qquad y_{{\rm aux},n}=Y_n.
  \]
  The seed identities \(U+p=jc\) and \(U+c=of\), together with the congruence modulo \(cf\), make both quotients integers. All their numerators and denominators are strictly positive, so all three new coordinates are positive integers.
- **Source equations:** The reconstructed coordinates satisfy \(j_nc-p=U_n=o_nf-c\). The preserved norm gives exactly \(R^2(U_n^2-Y_n^2)=1-Y_n^2\). All other comparisons retain their seed values by the dependency audit.
- **Infinitude:** One application of \(B\) maps a positive vector to
  \((RV+DY,V+RY)\), with both coordinates strictly larger because \(R>1\) and \(D>0\). Since \(L\ge1\), both \(V_n\) and \(Y_n\) strictly increase with \(n\). The reconstructed positive witness tuples are therefore pairwise distinct.

The alternative seed-unit matrix \(T=\bigl(\begin{smallmatrix}RU&DY_0\\Y_0&RU\end{smallmatrix}\bigr)\) likewise has determinant one, and its powers \(1+nL\) give the originally proposed construction. Its factorial-order argument and all congruence deductions are valid too.

## 4. Scope and qualifications

- This is a seed-relative theorem: **every nonempty fiber is infinite**. It does not assert nonemptiness for inadmissible ports or scale. For a domain where prescribed-scale completeness supplies a positive seed, infinitude follows immediately at that same prescribed scale.
- No height change, change of outer history, source recompilation, additional witness coordinate, or operation-count increase is used.
- Derived native register values in the nine listed gates generally change; the entire arithmetic source must be evaluated with the reconstructed witnesses. It would be inaccurate to say every other gate value stays fixed.
- The proof establishes mathematical infinitude directly. It neither materializes a gigantic canonical Pell seed nor requires executing third-party Python or a numerical witness search.

Independent review completed 2026-10-03.

## 5. Final-deliverable review

I reread the completed `THEOREM.md` and inspected and ran the locally authored `check_native_fibers.py`. **Final verdict: PASS; no mathematical issue found.**

- The theorem's direct inequality chain is valid: `q>=16`, `s>=3`, `k>r+1`, and positive `eta` imply `c=(sq)k+eta>48(r+1)>2r+1`. Thus `U>0` and `R>1` require no implicit canonical-index assumption.
- Its fixed-outer lift is justified by transitive dependency tracing, not merely a direct-name search: the only affected comparisons in the full fixture are comparisons 15–16 (native comparisons 13–14). Every nonnative comparison is unchanged. The inherited cleaned-time bridge uses only fixed outer endpoints and the fixed native clock, as the upstream three-mass interface explicitly states; it adds no dependence on the three varied native coordinates.
- The actual written proof correctly distinguishes the unchanged auxiliary norm `R^2=(a^2+4a+3)(f^2-1)` from the norm being varied. Its congruence division by `R` is justified by divisibility modulo `Rcf`; it assumes no coprimality of `c,f`.
- The prescribed-scale AND64 source explicitly inherits the full positive extension at the same fixed coordinates and states its domain, including the admitted smallest scale. The theorem restricts seed existence to valid AND/scale ports and excludes the separate zero-step no-witness case appropriately.
- The local checker returned `PASS`: four fixture dependency audits, five auxiliary-family terms, and modular matrix order 12 for the small test. Its toy tuple is prominently and correctly described as an auxiliary-system example, not a complete native witness. It reads upstream JSON as inert data and executes no upstream code.
- I independently recomputed all four local Markdown snapshot byte counts, SHA-256 hashes, and Git blob SHA-1 hashes and matched `source/provenance.json` exactly. This verifies snapshot integrity against the stated pinned provenance.

No additional circuit operations or coordinates are concealed in the recurrence: these are witness-construction formulas outside the existing source. The claimed infinitude follows from the proof, not the finite checker samples.
