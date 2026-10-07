# Reproducibility and verification

## Dependencies and output policy

Mandatory replay uses only Python 3.10+ standard-library modules, integer arithmetic, and `fractions.Fraction`. Mandatory PDF builds additionally require an installed `pdflatex`, `kpsewhich`, TeX distribution, packages and fonts used by Report195.tex. If the distribution lacks a prebuilt local format, the builder can initialize one with the installed `pdftex` and installed font maps. No dependency is downloaded or installed.

`--symbolic` explicitly adds the optional installed SymPy dependency. Without that flag, the symbolic script is shipped but never imported or executed. With it, the first- and second-correction symbolic outputs are regenerated in both normal and optimized modes and byte-compared; both resulting transcripts are included in the release. No copied transcript is treated as a new run.

Every persistent output must use a fresh absolute path outside the package. Its parent must already exist. Paths containing `..`, relative paths (including `../build`), file or directory symlinks at any path component, existing outputs, and outputs inside the package are rejected. The builder stages work in a temporary sibling directory and exclusively creates the final directory only after checks pass. Existing files and directories are never removed or overwritten. The source tree is checked before and after execution and never intentionally modified. Every source file must be valid UTF-8 with no C0 control bytes other than tab and newline; this catches accidental string-escape corruption in TeX.

Run commands with `-B` as shown in README.md. Scripts also disable bytecode generation before importing local modules. Deliberately closed inventories reject Python caches, unlisted files, empty directories, FIFOs, symlinks and other nonregular entries. Keep unrelated files outside the source package.

## Positive dynamic program

Immediately before processing part size j, row d[k][s] counts partitions of s with exactly k distinct sizes, all greater than j. Adding size j with positive multiplicity contributes

    e[k][s] = sum(r>=1) d_old[k-1][s-r*j]
            = e[k][s-j] + d_old[k-1][s-j].

The code updates k in descending order, preserving d_old[k-1], and adds e[k] to d[k]. If k=j it adds e[j] to the answer: these and only these partitions have minimum j and exactly j occupied sizes. Each admissible partition is counted once, at its minimum. All arithmetic and summation are positive.

The least possible total for k distinct sizes at least j is k*j+k*(k-1)/2. The largest possible target minimum is floor((1+sqrt(1+24*N))/6), because j+(j+1)+...+(2j-1)=j*(3j-1)/2. The implementation uses `math.isqrt` and discards only impossible states. It regenerates a(0),...,a(1500); a(0)=0.

The independent check generates ordinary nondecreasing partitions recursively and tests `minimum == len(set(parts))` directly for n=0,...,35. It shares neither the DP state nor its recurrence. The source-data comparison uses only the 58 actually observed live OEIS display terms, not an unobserved b-file.

## Rational certificates

1. First correction: a=log(3/2)=2*atanh(1/5). A geometric majorant for the terms after k=1 gives a<3041/7500<811/2000. For Q(x)=26*x^2-82*x+29, Q is decreasing on [0,1] and Q(811/2000)=48373/2000000>0. Hence B=-Q(a)/(144*(a-1)^2)<0. The report's S=Li2(2/3)-Li2(1/3)+a*log(2) is positive termwise, so c=B*sqrt(S)-3/(16*sqrt(S))<0. The exact rational inequalities are mandatory checks; no fitted or floating sign inference is used.
2. Interior zero: G(q)=F(q)/q is evaluated through degree 1000 by exact rational Horner evaluation. Since a(n)<=p(n), P(R)<=b^b at R=(b-1)/b implies discarded tail <=(r/R)^(1001)*b^b/R. With (r,b)=(3/4,5) and (4/5,6), both bounds are below 10^-12. Exact comparisons prove G(-3/4)>1/4 and G(-4/5)<-1/2. Continuity therefore yields a real zero in (-4/5,-3/4), excluding a finite eta quotient after monomial normalization and any product known to be holomorphic and nonvanishing throughout the disk. This does not exclude sums of products or q-hypergeometric identities.
3. Euler transform: exact exponents through degree 200 exclude pure periods 1,...,50 within those finite observations. This is not a proof against all eventual patterns.

The optional Wick script independently constructs two- and three-dimensional Gaussian contraction formulas and symbolically checks B and the additional -3/(16*S) correction. The separate `second_wick_check.py` computes the next finite contraction through phase degree 6, log-amplitude degree 4, and first Euler–Maclaurin degree 2. It explicitly checks B2=(676*a^4+3416*a^3-10200*a^2+22172*a-7559)/(41472*(a-1)^4), d2=B2-15*B/(16*S)-15/(512*S^2), and c2=S*d2. Its speed coordinate is D=X+a*Z, so v-a=D+D*Z-a*Z^2; it checks covariance against the differentiated phase Hessian. These programs compute the first two corrections, not an unrestricted all-orders coefficient engine. Their exception checks remain active under optimization. They do not prove localization, tail estimates, or analytic transfer. The second coefficient calculation requires degree 6/4/2 to identify the coefficient; the written remainder proof additionally uses existence and parity of the next odd jet, not merely those finite cutoffs.

## Receipts and manifest

Every replay regenerates `exact_terms.txt` and `exact_checks.json` in normal and `python -O` subprocesses using `-I -S -B`, then compares complete bytes. `-S` prevents site-package imports in mandatory calculations. `RESULT.json` records their sizes and SHA-256 hashes, normal/optimized agreement, the n=1500 bound, and whether symbolic verification was explicitly requested. A release embeds one copy of these identical results and the replay receipt.

Every build runs tailored safety guards in normal and optimized subprocesses, compares their receipts, regenerates exact replay, and invokes pdfLaTeX twice with shell escape disabled, fixed epoch 1791072000 (2026-10-04 UTC), UTC locale settings, and private cache/home directories. Auxiliary files must stabilize and references must resolve. Overfull boxes and LaTeX warnings fail the build. The final PDF is checked for its PDF signature.

ZIP members are sorted, stored uncompressed, stamped 2026-10-04 00:00:00, and assigned regular-file permissions 0644. The manifest checks a closed inventory, per-file lengths, SHA-256 hashes, strict JSON keys/types, bounded aggregate bytes, and regular nonsymlink files. The manifest does not hash itself. ARTIFACTS.json separately records hashes of the delivered TeX, PDF, and ZIP. Hashes detect modification relative to a manifest; they do not authenticate a maliciously replaced manifest and payload.

The integration test runs real normal/-O builds, compares TeX/PDF/ZIP/artifact-receipt bytes, extracts only the exact expected regular-file inventory, verifies the extracted manifest, regenerates exact receipts from the extraction, and rebuilds it. Byte identity is promised only for identical sources with the same installed Python/TeX/font stack, not arbitrary versions or platforms. Optional symbolic text likewise depends on the installed SymPy version. Use `test_build.py --integration --symbolic` to run the same complete deterministic-build and extracted-replay checks with the symbolic transcript included; use the same `--symbolic` choice when comparing original and rebuilt release bytes.

## Scope and limitations

This is an offline reproducible research package, not a sandbox for executing untrusted Python or TeX. It makes no network calls but does not configure an operating-system network firewall. The installed toolchain and source code must be trusted. Checks protect ordinary path mistakes, unexpected contents, symlink inputs, accidental stale receipts, and optimized-away assertions; they do not promise defense against an adversary concurrently replacing arbitrary filesystem ancestors.

Exact finite counts and rational certificates do not prove the coefficient asymptotic, the all-orders expansion, or an effective onset. Those analytical claims and their hypotheses are in the report. No interval-certified decimal constants, error threshold, or novelty certificate is inferred from the computed table.
