# Sharing the existing lower-transport sum gives the complete U9 compiler in 243 operations

The complete 244-operation U9 construction has an algebraic successor
with **243 = 129M + 114A** operations, the same **43 positive witnesses**,
and degree **at most 936**. The polynomial itself is unchanged on every
supplied tuple. Both ordinary-input interfaces, all fixed numeral
recipes, and the positive domains are identical. The separate universal
84-operation bound is unchanged.

The new saving reuses an addition already paid for in lower transport.
It was proposed by the preceding research agent and relayed by root;
this note supplies the complete source edit, consumer check and proof.
There is no new selector substitution or carry premise.

## 1. Exact local identity and its complete boundary

Use the names of the frozen 244 source. Abbreviate

    g    = hist__global_bound,
    S0   = hist__S0,
    Sh1  = hist__Shat1,
    Zv1  = hist__ZVhat1,
    Rest = hist__global_sum__13 = HU + HV + ZU + ZV0.

The parent size cone is

    group_global_slack = g + Sh1,
    groups_size_slack  = group_global_slack + S0,
    global_sum14       = Zv1 + Rest,
    P                  = groups_size_slack + global_sum14.       (1)

Its independent lower-transport cone already contains

    linear_group169 = Sh1 + Zv1,
    linear_coefficient170 = 6 * linear_group169.                  (2)

Keep both rows of (2), edit exactly the following two rows of (1), and
delete `group_global_slack`:

    groups_size_slack = g + S0,
    global_sum14      = linear_group169 + Rest.                   (3)

The retained row for P then computes

    (g + S0) + ((Sh1 + Zv1) + Rest)
      = ((g + Sh1) + S0) + (Zv1 + Rest).                          (4)

Equation (4) is an identity over every commutative ring; it needs no
sign, integrality, compiler equation, selector condition or program
validity. The two edited intermediate values need not equal their old
values separately. It is their common complete boundary P that agrees.

The complete parent arrays have precisely these consumers:

| Parent name | All direct consumers |
| --- | --- |
| `group_global_slack` | `groups_size_slack` |
| `groups_size_slack` | `hist__P__10` |
| `hist__global_sum__14` | `hist__P__10` |
| `hist__linear_group__169` | `hist__linear_coefficient__170` |

In the child, `hist__linear_group__169` gains just
`hist__global_sum__14` as a consumer. The other two surviving internal
outputs remain private to P. The shared addition itself is unchanged,
so its old lower-transport consumer still receives the identical value.
The deleted intermediate has no external consumer.

Consequently P is the only exit whose equality needs proof. Every
retained operation outside this cone has the same operands, and every
numeral recipe is identical. A topological induction after (4) proves

    F243(all supplied coordinates) = F244(the same coordinates). (5)

This argument covers the entire output, including the last charged
subtraction. It is not merely an identity after imposing halting or
native constraints. Both complete source arrays explicitly contain the
whole inherited loader, histories, predicates and endpoints.

## 2. Positive domains, soundness, completeness and degree

All supplied coordinates are unchanged. In particular the positive
size sum is still

    P = HU + HV + ZU + ZV0 + Zv1 + g + Sh1 + S0.                  (6)

All eight summands are paid and positive, exactly as in 244. Nothing is
removed from the bound used there for raw selector digits. Therefore
its signed-prefix argument, dyadic recovery and nested-carry proof
remain applicable verbatim. The two selector bounds are still recovered
in the order established there; this source change does not assume
either one earlier.

More directly, (5) gives the identity bijection between positive zero
tuples of the two complete polynomials, even for arbitrary supplied
parameter values. On valid U9 program slices the complete 244 theorem
then transfers both soundness and completeness. In particular every
recursively enumerable set of positive integers retains the ordinary
input criterion with four effective fixed program parameters and 43
positive existential witnesses. The separate five-program-parameter
interface is retained as well. No existence of a matching word or zero
is asserted on a rejecting input.

The degree bound at most 936 follows from exact equality with the
complete parent polynomial. It is not a source-array degree calculation
and is not an assertion that the degree is exactly 936. No bound on the
separate 84-operation construction changes.

## 3. Complete arithmetic count and verification scope

Each 244-row parent loses one addition and gains no operation. There
are two edited row records and 241 literally retained records, giving
243 rows: 129 multiplications and 114 additions or subtractions. The
retained existing addition in (2) has two consumers and is charged once.
A static topological reorder places it before its new size-cone use.
No supplied port, operation or fixed numeral role becomes dead.

Both complete sources are saved in the receipt: 486 child rows in all,
with the unchanged 43 positive witnesses and ten fixed numeral roles
in each. Before the retained last subtraction, the certificate costs
**242 = 129M + 113A**, followed by one comparison with the already paid
geometry discriminant. This certificate count is separate from the
243-operation polynomial count.

The fresh author helper performs only byte authentication, inert source
editing, shape/count/topology/liveness checks, complete consumer guards,
and one independent handwritten linear identity. That identity compares
the eight integer coefficients of the two expressions in (4); it takes
no source array as input. It yields coefficient vector
`[1,1,1,1,1,1,1,1]` on both sides. The universal ring identity is proved
above and does not rest on numerical sampling.

The original helper wrote its receipt and matched it in normal and
optimized Python modes from `/`, all before freezing. No predecessor,
supplied, archived or frozen program was executed or imported. No saved
source array was evaluated numerically or symbolically, and no degrees
were propagated through it. The complete 244 proof and helper were read
inertly; both full parent arrays were structurally checked. The proof
scope here is the exact algebraic replacement of that complete parent,
not a fresh audit of its earlier machine, native or Pell constructions.

No wrong or unproved claim was introduced or suppressed in this draft.
The parent retains its two numbered counterexamples concerning an
unpaid selector bound and omission of the nested carry; (5) preserves
its requirements. No minimality claim is made for 243 operations.

Evidence SHA256:

- Helper: `b75fccf5996c790bd5ce254d11ab0fe907cb5cdb7b3470aaef7988286f7371e4`.
- Receipt: `db9673ba90ca965273a961f6bfb7c03f0e0a512ec0850c2841be3091bdcc3620`.

Pinned dependencies under
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue`
are listed below. Before repository installation the identical same-name
frozen `/tmp` bytes are allowed. A byte pin does not enlarge the stated
proof-read or static verification scope.

| Dependency | SHA256 |
| --- | --- |
| `neary_woods_positive_groups244_tesla.md` | `8f4bcdb21a1202c618de0e2b6cd9cb3f5d83372cf9ab83f59ee8f32d3701ff07` |
| `neary_woods_positive_groups244_tesla.py` | `21bfe676106749fefe71bd0f5b32e3cd8689f3e68c24f4798782fb717750d203` |
| `neary_woods_positive_groups244_tesla.json` | `59fb18b0cda52249afab70bf7e2952e80378ab41961e299d809dfa20e322003b` |
