# The Möbius function in intuitionistic primitive recursive arithmetic

Read **mobius_ipra.pdf** for the complete argument. The source article inventory is in section 13. Theorem 9.1 gives an explicit Mertens bound, and the following theorem gives ordinary convergence of the three boundary moments. Theorem 10.1 gives the two-way connection with the prime number theorem.

## Rebuild the paper

Run the following commands in the extracted directory with TeX Live and the Latin Modern fonts installed.

    pdflatex -interaction=nonstopmode -halt-on-error mobius_ipra.tex
    pdflatex -interaction=nonstopmode -halt-on-error mobius_ipra.tex
    pdflatex -interaction=nonstopmode -halt-on-error mobius_ipra.tex

The main file inputs the other eight .tex files in this directory. No bibliography processor or network lookup is needed.

## Reproduce the finite checks

    python3 checks.py
    sh lean/check.sh

The Python program uses the standard library; its recorded output is in checks.txt. It compares the sign and factor-count lists to the two source articles and tests sample cases of the finite formulas. The Lean command checks the standalone universal proofs with Lean 4 installed. The lean/README.md file gives the versions used and instructions to replay the separate ProveIt import audit in a configured upstream checkout.

## Proof status

The finite and quantitative proofs in the paper are human arguments in the indicated first-order interpretation. The standalone Lean files were compiled and use Lean integer and natural-number operations. The pinned ProveIt modules contain embedded iPRA derivations for the divisor-cancellation and inversion core, among other results. The upstream audit was source-inspected and was not rerun here. Section 12 specifies the additional object-theory deductions needed for a full mechanization, including for the analytic estimates.
