# Compute paid native fields: AND90, Wang motion223 and toggle137

Six positive native coordinates are already defined by paid arithmetic
gates. Replacing their supplied values by those registers removes six
comparisons and six witnesses, with no change in certificate cost. After
the [positive scale change](native_binary_positive_scale.md), the complete
prescribed-AND polynomial costs **90=42M+48A**, with **9 comparisons and
15 positive witnesses**. Its total degree is **44**.

The same graph substitution gives **223=93M+130A** for the complete
[Wang motion component](wang_b_packed_motion.md), and **137=59M+78A** for
the complete [toggle component](langton_ant_packed_toggle_tape.md). Their
degree bounds rise to696 and256. A four-coordinate option preserves the
earlier bounds316 and124 at229 and143 operations respectively. These
are components with unchanged endpoint relations and missing instruction
or ant control, not new universal recognizers. The complete U9 and
separate75/87 bounds are unchanged.

The [source](native_binary_computed_fields.py) and
[receipt](native_binary_computed_fields.json) retain all parent artifacts.
They enumerate every subset of these six definitions for standalone AND,
with and without the scale change. They also emit the four/six choices
for both history components.

## 1. Six positive graph coordinates

Write q for the native scale, X=wq in the raw core and X=q(r+b) after
the positive scale change, Y=sq, and E=XY. The actual defining registers
are

| Supplied coordinate | Paid expression | Literal register |
|---|---|---|
|s|2*odd_half+1|bs_odd|
|k|eta+zeta|R10b|
|a|E+Y=Y(X+1)|R12|
|c|kY+eta|R10a|
|d|X+ac+ga*(4a+3)|R14|
|r|F0+q*F1+q^2*F2+q^3*F3|bs_packed|

The three callers prove q>0 and F3>0 on all positive supplied tuples,
before any native equations. For standalone AND, q=16P and
F3=16Zhat-8>=8. For both packed components the joined output Z is
nonnegative before typing, so F3=16Z+8>=8. The Wang source has
J=Ihat+Lhat+Rhat+Stayhat-4>=0, D>=5 and
P=(8D-1)J+1>=1; its scale is8D*P^12. The toggle source has D>=3,
J>=1, P=(4D-1)J+1 and scale4D*P^4. Thus each has q>=16
independently of every removed comparison.

Every remaining supplied native coordinate is positive. In the raw
case X=wq>0; after the scale change, r+b>0, whether r stays supplied
or becomes its positive packed definition. It follows successively
that s,k,r,X,Y,a,c,d are positive. No checksum, bit typing, ratio or
Pell conclusion is used for this graph-positivity argument.

One can therefore replace any subset of the six coordinates, not only
the two displayed subsets. The source substitutes every use, deletes
exactly the defining comparisons, removes exactly those supplied
coordinates, and topologically sorts the retained gates. It checks the
actual native kernel rows and comparisons, unique definitions, all
operand availability, the complete arithmetic histogram and that every
emitted gate reaches the final output. The dependency graph remains
acyclic even when r is computed before the positive-scale X gate.

The generic algebraic helper states its positive q,F3 domain contract;
it does not infer positivity for an arbitrary caller from register names.
The three concrete callers above establish that contract.

## 2. Bijection on full positive zero sets

Given any positive tuple for the new source, evaluate the six paid
definitions that were selected and restore the missing coordinates to
these values. Section1 proves that the restored coordinates are positive.
Every new source register agrees with the corresponding parent register
on this extension. Each deleted residual is zero identically; all
retained comparison residuals agree individually. Consequently

    SOS_new(v)=SOS_parent(Graph(v))

holds for every integer supplied assignment, including signed assignments
away from zeros. In particular every positive new zero extends to a
positive parent zero with the same parameters and supplied outer history.

At a positive parent zero its defining comparisons give precisely these
graph values. Erasing the selected coordinates therefore gives a new
zero; extending it returns the original tuple. Erasure and graph extension
are inverse on the entire positive zero sets, not only on canonical
native witnesses. The complete prescribed AND relation and both complete
history relations are preserved.

When the parent already uses the positive scale change, the two maps
compose in that order: first restore the computed coordinates to the
scale parent, then use that parent's scale lift to the raw source.
Both forward extensions are positive on the full positive domain. The
inverse scale inequality at parent zeros is inherited from its reviewed
exponential/popcount theorem. The metadata records the two distinct
parents; the scale helper is called on its original parent packet, not
on a later packet whose r is no longer a supplied coordinate.

## 3. Literal component costs and degree tradeoffs

The four-coordinate choice is a,d,k,s. The six-coordinate choice adds
c,r. Let C be the raw certificate cost, e its comparison count and w
its witness count. With b in{0,1} denoting the prior scale change and
t the number of computed fields, the resulting counts are

    certificate C, comparisons e-b-t, witnesses w-b-t,
    SOS operations C+3(e-b-t)-1.

Each erased definition removes one subtraction, one square and one
accumulation addition from the complete polynomial. All fixed-numeral
multiplications and every graph-defining gate remain charged.

| Component | Scale changed | Fields | Certificate | Comparisons | Witnesses | Polynomial | Degree bound |
|---|---|---|---:|---:|---:|---|---:|
|AND|No|Four|64|12|18|99=45M+54A|28|
|AND|No|Six|64|10|16|93=43M+50A|44|
|AND|Yes|Four|64|11|17|96=44M+52A|28|
|AND|Yes|Six|64|9|15|90=42M+48A|44|
|Wang motion|No|Four|188|15|31|232=96M+136A|316|
|Wang motion|No|Six|188|13|29|226=94M+132A|604|
|Wang motion|Yes|Four|188|14|30|229=95M+134A|316|
|Wang motion|Yes|Six|188|12|28|223=93M+130A|696|
|Toggle|No|Four|105|14|24|146=62M+84A|124|
|Toggle|No|Six|105|12|22|140=60M+80A|228|
|Toggle|Yes|Four|105|13|23|143=61M+82A|124|
|Toggle|Yes|Six|105|11|21|137=59M+78A|256|

Certificate histograms are unchanged:33M+31A for AND,81M+107A for
motion,48M+57A for toggle. All parameters have degree1 alongside the
supplied witnesses. Degree bounds propagate through the actual source;
no equation holding only on zeros is used to lower them.

For standalone AND, all128 subset/scale schedules have exact degree
certificates: the propagated multivariate upper bound equals the degree
on an explicit affine univariate slice. Each slice evaluates every paid
gate with exact integer polynomial arithmetic. The largest residual
degree d gives a nonzero positive leading coefficient in its sum of
squares, establishing a lower bound2d on multivariate degree. Equality
with the upper bound proves the reported exact degree. The generic ledger
still labels its propagated value as an upper bound; the separate
`degree` record supplies the exact standalone assertion.

The exhaustive standalone operation/degree frontier in this restricted
128-schedule family is

    90/44,93/40,96/28.

The middle option computes a,d,k,r,s after changing the scale, leaving
c supplied; it has10 comparisons and16 witnesses. The96/28 point can
compute those same five fields without the scale change, or use the
four-field scaled option shown above; both have17 witnesses. This finite
enumeration does not optimize other native arithmetic, product finalizers
or arbitrary Diophantine representations. No exact degree is asserted
for the two history components.

## 4. Verification and retained semantic limits

```sh
python3 native_binary_computed_fields.py
```

The checker records2,816 complete graph-substitution/output identities,
including1,408 signed assignments and1,408 positive graph extensions.
All128 standalone schedules and twelve representative component schedules
receive source-closure and literal ledger checks. The positive-scale
cases additionally compare with the original raw polynomial after the
two composed coordinate lifts. All128 standalone degree slice witnesses
are exact and reach their propagated bounds.

Another128 genuine outer histories, totaling416 chronological rows,
transfer through the graph changes. They retain every outer comparison,
the exact joined AND relation, canonical scale bounds and positive graph
coordinates. Their native entries are placeholders; they are not full
positive Pell zeros. The inherited converse and positive bijections
prove existence of full native extensions for every valid history.

The motion endpoint relation remains exactly monotone tape extension
with dyadic initial and final heads. It still lacks the finite program
controller, branch conditions and ordinary input bridge. The toggle
endpoint relation still admits every pair of nonnegative tapes; it lacks
planar ant motion/turning, periodic hardware, the ordinary input map and
acceptance. Reducing native bookkeeping cannot supply these missing
computational constraints.

Author writer and fresh default replay passed. An independent reviewer
completed the full proof/source/fresh-default review with no findings.
A separate literal executor and independently written graph formulas
checked640 full source/residual/output identities,320 signed and320
positive, covering all128 standalone choices and eight motion/toggle
choices. Scaled cases also restored the raw parent with a manual scale
map. The review checked all standalone degree witnesses and the finite
frontier, positive dependency order and composed coordinate bijections.
