# Short-circuit search: retained frontiers and rejected shortcuts

Reference commit: `22e75dd6b87b1b199bb08c778d7cf075ae5aae08`.
Reference package: `36-small-tuple`, in the repository's
`con-zfc-diophantine-forms` collection.

This audit found **no proved improvement below the inherited 67-operation
single equation or 59-operation system**. It is not a new candidate.
The exact reference JSON files are copied into `upstream/` as data. Their
coefficient binding still refers to the complete package36 tuple; the files
are not standalone numerical instances in this small audit directory.

## The actual obstruction in the product construction

Let Delta denote the main Pell discriminant, and put I=i c^2. The scaled
strong factor in P67 is

    Delta f^2 - (Delta I)^2 = Delta (f^2 - Delta I^2).

The entire product equals Delta. Its strong factor is identically divisible
by Delta, independently of all equations. Cancelling Delta therefore leaves
a product of integers equal to one, after which unit-sign arguments apply.

It is tempting to replace this by the ordinary strong factor

    Delta f^2 - I^2,

while leaving the product's right side equal to Delta. This factor is not
identically divisible by Delta. The equation merely says it divides Delta;
it does not say it equals Delta times an integer unit. For example the
polynomial values Delta=8, f=1, I=2 give the proper divisor 4. This example
is only an obstruction to the cancellation argument, not a counterexample
to the full authentic compiler instance. The ordinary strong system uses
an explicit equality I^2=Delta(f^2-1), so it does not have this problem.
Any use of the unscaled product needs a genuinely new semantic argument.

## Other exact transformations checked

1. Factoring the packed index through J is valid but does not save gates.
   With q=beta J+1 and G=(q-1)(q-F)+alpha,

       G(q^2-1)+(MC+q MF)J
       = J[beta G(q+1)+MC+q MF].

   Once q^2 is already needed for q^3, the original outer expression uses
   six binary gates (q^2-1, its product with G, q MF, addition MC,
   multiplication J, final addition), whereas the factored expression uses
   seven. Precomputing MC+MF and substituting q=beta J+1 gives another
   seven-gate expression, not a saving.

2. Shifting the first Pell root tau=L+r gives the exact equation

       r^2 + L(2r-k) = 1.

   This replaces four gates for tau^2-L(L+k) by five gates. It can lower
   some formal degrees in other presentations, but does not improve this
   evaluator. An extra positive gap coordinate requires another constraint;
   counting it as free would be incorrect.

3. For the main Pell norm, write B=X+gamma H and D=ac+B. Then

       D^2-(a^2+H)c^2 = B(B+2ac)-Hc^2.

   This cancellation is exact. It does not remove the need to compute
   Delta=a^2+H, because the ordinary strong equation uses Delta again.
   The apparent saving from deleting Delta is thus not live-circuit saving.

4. Replacing the auxiliary Pell pair by y=V+r gives

       I^2(V^2-y^2)+y^2
       = (V+r)^2-I^2 r(2V+r).

   The right-hand side costs more gates under the existing sharing. It also
   requires proving r positive before interpreting r as a positive variable.

The accompanying authored checker verifies these polynomial identities and
the exact gate counts/liveness of the two copied schedules. These checks do
not prove the inherited compiler semantics and do not decide Con(ZFC).

## A useful research target

The first-index Pell certificate is used not only to manufacture a power:
it bootstraps a large Pell index before the strong-rank recovery theorem is
applied. Removing it requires replacing that bootstrap, not merely dropping
one residual. A new index theorem that simultaneously supplies the large-rank
bound and the power relation would be a structural improvement; none is
established in this audit.

New audit text and checker: AI-assisted work for ProveIt, released under
MIT-0. Upstream reference data retain the repository's attribution and
licensing. This note has not undergone external human review.
