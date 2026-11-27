# Dirichlet zero packets and quadratic Euler factors

Research notes dated 26 November 2026. Both papers have self-contained LaTeX sources. The archive contains their compiled PDFs, exact finite verification programs, and recorded outputs.

## First paper

Read **zero-packets/zero-packets.pdf** for the answer to the composite-exponent measurement question in ProveIt's *What zero differences forget about Dirichlet characters*. A packet is a multiset of Dirichlet character twists. At a prime, its twist values give a histogram on a cyclic group of order E. For known mass, the exact worst-case number of individual balanced Fourier products for recovery up to rotation is

    fixed list       (tau(E)^2 + tau(E) - 1 - tau(E^2))/2
    adaptive list    tau(E) - 1.

Here tau counts positive divisors. The fixed list also achieves the least possible maximum order, which is at most six. Section 6 proves a sharp one-measurement threshold for small prime-power packets. Section 7 gives recovery from every sufficiently high logarithmic window of relative zero ordinates. The height constant depends on the family and prime. The last page realizes the order-six obstruction with primitive characters modulo 61.

## Companion paper

Read **prime-traces/prime-traces.pdf** for the exact matching densities of two different products of k quadratic Dirichlet L-functions. The minimum prime-disagreement density is 2^(-d) with d the smaller of the available character rank and floor(log2(2k)). Section 3 determines all attainable densities strictly below twice this minimum. The density classification is unconditional. Section 4 uses Dirichlet GRH to show that a single smoothed prime count determines the exact density in the high-agreement range.

## Reproduce the finite checks

Run these commands from the top of the extracted archive with Python 3.10 or later. The scripts use the standard library.

    python3 zero-packets/check_probes.py
    python3 zero-packets/check_adaptive.py
    python3 zero-packets/check_rigidity.py
    python3 prime-traces/verify.py

Their outputs are recorded in zero-packets/check_probes.txt, zero-packets/adaptive_output.json, zero-packets/rigidity_output.txt, and prime-traces/verification.txt, respectively. The fixed schedules are tested through exponent 300. The bounded adaptive construction is separately tested on 291,702 configurations. The trace program checks 723,057 packet pairs and 95 explicit constructions through rank ten. These computations check finite algebra. They use no numerical approximations to L-function zeros.

## Rebuild the papers

With standard TeX Live packages installed, run the following commands in the indicated directory.

    cd zero-packets
    pdflatex -halt-on-error zero-packets.tex
    pdflatex -halt-on-error zero-packets.tex
    cd ../prime-traces
    pdflatex -halt-on-error prime-traces.tex
    pdflatex -halt-on-error prime-traces.tex

SOURCES.md identifies the requested sources, their roles in the proofs, pinned repository snapshots and the closest prior work found. The new theorems have written proofs. The upstream Lean proof and its independent verification are separately documented there. Historical priority for the exact combinations established here has not been independently established.
