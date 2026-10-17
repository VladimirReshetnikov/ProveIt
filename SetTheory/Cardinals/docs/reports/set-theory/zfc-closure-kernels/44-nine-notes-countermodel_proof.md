# Three exact countermodels to tempting FC15 row deletions

The recommended FC15* payload uses the two guard fusions F=H and S=Y and the
derived member term, hence nine proper function symbols and the displayed
fifteen universal clauses. The
following structures satisfy every row except the indicated single row. They
show that those deletions would destroy the calibration, rather than merely
change the proof technique. The code `check_countermodels.py` enumerates all
assignments in all fifteen rows for each model and independently verifies the
claims. Its output is `countermodel_results.json`.

## 1. Deleting the preserved-coordinate row has a three-object model

The domain is {0,1,2}, d=0, and the relations are

    E = {(2,1),(1,2)},
    Inc(s,t) iff t=1,
    G(b,t) iff t != 1.

Thus the three membership columns are respectively empty, {2}, and {1}.
Interpret the functions by

    V(s,j)=s,           C(s,j,z)=z,
    N(a,b)=0 if a=b=1, and N(a,b)=1 otherwise,
    A(j,k)=0,           Q(j,a)=a,          W(s,j,a)=0,
    H(b,t)=0,

and for every b,t use

| u | Y(b,t,u) | Z(b,t,u) |
|---:|---:|---:|
| 0 | 1 | 2 |
| 1 | 2 | 1 |
| 2 | 1 | 2 |

Then q=N(d,d)=1, the member term D*(x)=W(C(d,q,x),d,A(d,q)) is0, and
R(b,t,x,y) is simply t=1. Clause 01 holds because
V(C(s,j,z),j)=z. Clause 02 fails: taking s=0,j=0,z=1,k=1 gives k != j but
V(C(s,j,z),k)=1 != 0=V(s,k).

N computes the Boolean NAND of the truth values of class codes, so all three
NAND rows hold. A always denotes the false class because E(s,s) is false.
Since Inc ignores its first coordinate, Q(j,a)=a satisfies both existential
rows for every C and every W.

When t != 1, G is true and R is false; H=0 is empty. Every hull row is therefore
true. When t=1, G is false and R is the universal relation. For every proposed
subset bound u the table supplies an E-member Z of output Y lying outside u.
Thus all three counterexample rows hold. The hull rows are inactive in this
case. This proves every retained clause universally.

The failure is exact: changing one coordinate resets every coordinate. The
model cannot encode a general formula with simultaneously retained parameter
values. Distinct selector names alone do not repair this missing operation.

## 2. Deleting the updated-coordinate row also has a three-object model

Keep all preceding interpretations except put

    V(s,j)=0,           C(s,j,z)=s.

Then the retained-coordinate row 02 holds because both evaluated values are
0, while row 01 fails whenever z != 0. E(V(s,j),V(s,k)) is E(0,0), hence false,
so the atomic rows remain valid. Inc still ignores its first coordinate and
R is still equivalent to t=1, so all other verifications are unchanged.

Thus both pieces of Change are individually necessary for this target. This
is not a statement that every possible finite-class presentation must use
these exact syntactic rows; it rules out the concrete proposed deletions.

## 3. Extensionality does not repair either deletion

The E-columns are different, so both three-object E-reducts satisfy ordinary
Extensionality. Indeed they also satisfy ordinary Foundation: every nonempty
set has its sole member as an E-minimal member inside it. (The relation has a
two-cycle externally, illustrating why Foundation alone in such a weak
theory does not rule out every external cycle.) For any unequal a,b choose
an element in the symmetric difference of their columns as the witness X(a,b).
This extends either model to both additional witnessed Extensionality rows.

Therefore the same countermodels apply to the seventeen-clause extensional
control after deleting the indicated Change row. No inherited raw-quotient
subtlety causes the problem.

## 4. Deleting the negative NAND row has a one-object model

The domain is {0}. Interpret all functions and d by 0 and all three predicates
E,Inc,G as true. Then both Change rows, both positive NAND rows, the atom and
existential rows, and all six guarded closure rows hold. The sole failed row
is

    NOT Inc(s,N(a,b)) OR NOT Inc(s,a) OR NOT Inc(s,b).

Its three literals are all false. This also satisfies witnessed
Extensionality because equality of any pair is true. The deleted row was the
part that forces a genuine Boolean complement at N(d,d), and hence the
distinct selector values used throughout the calibration.

## 5. Exact finite verification and consequence

The standalone semantic checker examined 621 clause assignments in each
three-object structure and 15 assignments in the one-object structure: 1,257
in total. It asserts that every retained row holds, that the deleted row has
a counterexample, and that the E-reduct is extensional. These are exhaustive
finite checks, not bounded searches for a refutation of FC15.

Each weakened finite theory has the explicit finite model just displayed, so
ZFC proves its consistency by the elementary soundness theorem. Consequently,
assuming ZFC is consistent, none of these weakened targets can have its
consistency provably equivalent in ZFC to Con(ZFC): such an equivalence would
make ZFC prove its own consistency. This use of second incompleteness does
not claim any state lower bound for a Turing machine.
