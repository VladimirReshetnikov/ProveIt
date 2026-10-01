# Factored affine transports with the identical polynomial

The paid transports in the [complete affine-pair history](pcp_uniform_affine_pair_history.md)
can share repeated coefficients and common linear forms. On the actual
34-tile odd-integer table, this saves **104 operations**, reducing its
history certificate from696 to592. The complete raw polynomial falls
from993 to889 and its [native-unit composition](gpcp_complete_fixed_program_units.md)
from918 to **814=317M+497A**. All these comparisons use the same
interleaved layout. The full polynomial, witness list and degree are
unchanged on arbitrary integer assignments, including signed ones.

The [planner source](pcp_affine_factored_transports.py),
[linear-form emitter](affine_history_linear_forms.py) and
[receipt](pcp_affine_factored_transports.json) expose the paid schedules
and all candidate counts. This is an arithmetic identity optimization,
independent of any one-hot or positivity theorem. It does not assert
an optimum circuit or instantiate a numerical universal table.

## 1. Group coefficients and share a common form

The two raw transports compute fixed integer linear forms. For example,

    L_U=sum_i a_i*ZUhat_i + sum_i c_i*Shat_i - sum_i(a_i+c_i).

For any repeated coefficient a,

    sum_{i in I} a*x_i = a*(sum_{i in I} x_i).             (1)

The right side pays one multiplication and |I|-1 additions, instead of
|I| multiplications and |I|-1 additions. Numerals are fixed compiler
constants, but every nontrivial fixed-numeral multiplication is still charged.
Zero terms and multiplication by one are aliases, as in the parent.

For two forms with coefficient vectors A and B, choose any fixed vector C:

    A*x=(C*x)+(A-C)*x,
    B*x=(C*x)+(B-C)*x.                                   (2)

Compute C*x once. Each remaining form pays its own additions and
coefficient products. Negative coefficients and differences are ordinary
integer source expressions; no supplied positive coordinate is used
to represent them. Equation (2) holds before any comparison or typing.

The planner emits six candidates: flat, coefficient-grouped, and four
grouped variants sharing respectively equal common coefficients,
the smaller absolute coefficient when signs agree, the first form's
coefficient, or the second form's coefficient. Shared coefficients are
chosen only on variables occurring in both forms. The constants at the
ends of the forms remain exact paid additions or subtractions.

Copy tiles and repeated rewrite lengths make both identities useful:
many selected values have the same slope, and the two words share much
of their offset computation. This benefit is established by actual
emitted DAG counts, not by treating a grouped sum as free.

## 2. Literal source replacement and accounting

Each candidate starts with the parent's paid DAG cache. Only identical
already computed instructions may be reused. It emits both linear forms,
redirects their original consumers, and removes instructions having no
path to a comparison or retained interface. The native64 instructions
are treated as opaque roots and must remain literally unchanged, in
their original order. A dependency audit verifies the resulting source.

The candidate records the two original and new form outputs. Equations
(1)--(2) prove their identity for every assignment, hence every redirected
consumer computes the same value. Removing unused instructions changes
no retained output. Thus every comparison residual is identical, not
merely equivalent at a zero. The final sum of squares is the same
polynomial. Applying the existing native-unit projection also preserves
this identity, because the same coordinate substitutions and finalizer
are applied on both sides.

The automatic option chooses the smallest actual operation count, then
the multiplication count and a deterministic mode name. The literal
parent is retained as a fallback. Both parent layouts are separately
compiled and scored. Selection between layouts retains the parent's
positive-predicate theorem; an identity claim between different physical
layouts is not made. The reported savings compare the same layout.

The generic `linear_forms` metadata contains a coefficient dictionary,
constant and output for each coordinate. A compatible complete history
can supply that metadata even if its selected products are grouped
differently. No property of those groups is used in the algebraic pass.
`replace_history` composes a compatible raw history with the paid GPCP
boundary, namespacing every local register and sharing only the three
endpoints. Its input loader and boundary source stay literal.

## 3. Exact examples

The raw history comparisons and positive witnesses are unchanged:
19 and3s+26, respectively. The polynomial costs its certificate plus56.
The unit successor still costs the raw certificate plus32, with10
comparisons and3s+20 witnesses.

| Fixed table, same chosen layout | Old certificate | Factored certificate | Saving | Raw polynomial |
|---|---:|---:|---:|---:|
|Singleton identity|114|114|0|170|
|Original three-tile illustration|161|159|2|215|
|Eight equal-slope copy maps|244|217|27|273|
|Four mixed maps|181|173|8|229|
|34-tile odd-integer machine|696|592|104|648|

For the complete odd-machine equation with a computed initial endpoint,
the raw result is728 certificate operations,54 comparisons,180 witnesses
and889 polynomial operations, still at degree8416. Its projected unit
result is737 certificate operations,26 comparisons,161 witnesses and
814=317M+497A polynomial operations, still at degree19782. Retaining the
initial endpoint supplied costs817 with162 witnesses and degree8040.
The smaller three-tile unit illustration falls193 to191 at degree956.

These particular tables are not universal. For any fixed table, the
same exact rewrite is available and its savings are reported by the
actual source. The independent universal75/88 frontier is unchanged.

## 4. Verification

The default replay checks960 complete comparison-vector and SOS
identities, including480 signed assignments, over five distinct tables,
both physical layouts and all six linear-form modes. Another128 signed
checks compare complete fixed-program polynomials, including both raw
and unit-projected versions and both initial-endpoint conventions.
The composed exact degrees are independently recalculated and agree
with their parents.

These finite checks audit the implementation of the unrestricted linear
identities. The equalities (1)--(2) and preservation of all retained DAG
outputs establish their arbitrary-integer scope. No new positive native
extension, carry assertion or kernel relaxation is assumed.

Independent reviews passed the source, proof and fresh default replay.
They added3072 signed arbitrary-coefficient emitter cases,384 signed
complete identities on sixteen separate slope-class tables, and864
signed complete identities on twenty-four further per-tile tables.
Review also prompted an explicit same-table assertion in the history
replacement API; the actual compositions all satisfy it.
