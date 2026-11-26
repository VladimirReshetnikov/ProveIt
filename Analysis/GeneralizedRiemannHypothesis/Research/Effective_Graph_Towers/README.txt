WHEN DOES THE SPANNING-TREE FORMULA START?

Read report.pdf. The report's main result is a terminating computation of the
eventual polynomial and the least level from which it always agrees with
the spanning-tree valuation of an integral abelian voltage tower.

Build the paper in this directory:
    pdflatex report.tex
    pdflatex report.tex
The included TeX chapters are loaded by report.tex. No bibliography tool
is needed. The Python scripts require Python 3.10+; the generic compiler
and resultant checker also use SymPy (tested with 1.14.0).

Graph input
    python tower_automaton.py 3 --graph honeycomb.json
This example has two vertices and three parallel edges with distinct
voltages. It returns P(X,n)=5X-2n-4 and least onset 0. The JSON edge list
uses [origin, terminus, integer_voltage_vector] for each unoriented edge,
using one chosen orientation. Repeated edges and loops are allowed.
Level 0 is the base. For a positive-level convention use max(1,least_onset).
Every cover is required to be connected to have finite spanning-tree valuation.

A Laurent polynomial can also be supplied as a JSON array of
[integer_coefficient, integer_exponent_vector] pairs. All vectors must have
the same positive dimension. This mode sums over NONTRIVIAL p-power torsion
points through level n. To include the trivial point, add its valuation
when it is finite. For graph determinant input, --trees C instead includes
the graph correction v_p(C)-d*n where C is the base tree count.
Use --levels N for exact finite levels without computing the full closure.
The full compiler computes the characteristic polynomial of an integer
matrix over ALL reachable states. Runtime and memory may grow sharply with
large inputs. No polynomial runtime bound is claimed.

Torsion zeros
    python first_zero.py 3 '[[1,[0]],[1,[3]],[1,[6]]]'
Returns the first zero at level 2 with exponent 1 (a primitive ninth root).
The first-zero command includes the trivial tuple at level zero.

Reproduce the checks from this directory:
    python check_resultants.py
    python verify_delayed_tower.py
    python verify_leading.py
    python verify_grover.py
The first command recomputes the five exact law records in dv_examples.json
and tests other inputs by independent cyclotomic norms. The other commands
print the results recorded in the corresponding text files. They check the
examples by direct cyclotomic arithmetic, spanning-tree cofactors, and
quantum-walk matrices as described in the report.

These are proofs and independent arithmetic checks. The extension has not
been formalized in Lean. The linked GRH project is not a build dependency.
