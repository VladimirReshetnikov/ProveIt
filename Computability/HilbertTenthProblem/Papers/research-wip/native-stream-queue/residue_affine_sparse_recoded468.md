# Recoded one-program U21 compiler with 468 operations

The complete [source and receipt](residue_affine_sparse_recoded468.json)
cost **468=171M+297A operations**, with **67 positive witnesses**, ordinary
positive input x, the single fixed program parameter E=3^e, and degree
**at most5091**. The certificate costs **448=164M+284A**, with seven
comparisons in the inherited convention. Every emitted row and supplied
port is live.

The immediate parent is the actual
[one-program471 source](residue_affine_sparse_shared471.md). The new source
changes its injective control-state codes and arithmetic schedule. Its
**supplied positive integer zero set is identical** to that parent's zero
set. The full polynomials have the explicit correction in Section4; they
are not asserted equal at arbitrary inputs. This result does not change
the separate universal84 bound.

## 1. Literal interface and retained shared base

The [standalone helper](residue_affine_sparse_recoded468.py) authenticates
nine inert dependencies. It reads the saved471 array directly; it does not
run or import any predecessor. The supplied interface remains exactly E,
x and67 positive witnesses. The retained height/radix rows are literal:

    height_83 = program + input
    height_85 = height_83 + height_slack
    radix_86 = 64 * height_85.

Thus h=E+x+eta>=3 and B=64h>=192 before any typing argument. Both height
additions and the multiplication by64 remain paid. There is no additional
radix-program parameter. The valid represented-set recipe remains fixed
E=3^e and ordinary positive x.

The actual shared base is computed by ancestor closure of
`sparse_all_units` and ordinary residuals0,2,3,4,5, omitting only the
control comparison and its downstream finalization. This retains
**389=142M+247A rows**, including those five residual producers. In
particular, control-named state/target pair sums now used by prime selectors
or population J remain paid. They are not classified as private merely by
their names. Every one of these389 definitions remains literal.

The helper independently reconstructs all36 edges from the pinned21-row
U21 table and prime list(5,3,2,7,11,13,17,19), including the two loader edges.
The original body table has zero-based destinations; the control graph
shifts each destination upward by one, reserving state0 for the loader and
state22 for halt. The reconstructed complete edge tuples, including action,
prime and payload coefficients, must equal the pinned edge array. Every
actual selector is checked to be `E_i=edgei_hat-1`.

## 2. New valid codes and paid current-control word

In state order0,...,22, the selected codes are

    0,1,15,21,9,17,13,11,5,18,8,25,41,32,10,3,12,4,24,2,6,7,14.

They are pairwise distinct. Loader0 has code0; every body/halt code is
positive and at most41<B. The halt code is14. This is a selected finite
valid plan, with no code-choice optimality assertion.

Let G_p be the already-paid prime selector, I the increment selector,
L=E0+E1 the loader selector, and D_q the sum of outgoing edge selectors
from state q. The new body prime weights are

| Prime p |2|3|5|7|11|13|17|19|
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Weight w_p |0|1|2|3|8|9|17|11|

Use increment coefficient4 and state corrections

    d9=1, d11=16, d12=32, d13=32, d14=1, d18=16,

with all other corrections zero. The state code is
`w_prime+4*[increment]+d_q`. Consequently the current-control word is

    Cnew = G3+2G5+3G7+8G11+9G13+17G17+11G19
           +4(I-L)+(D9+D14)+16(D11+D18)+32(D12+D13).

All sums and scalar multiplications needed to evaluate this expression are
emitted or reused from paid rows. The existing population prefix
`u21_grouped_J_0=G3+G5` gives

    G3+2G5 = u21_grouped_J_0+G5.

The helper verifies both exact selector vectors and removes only the newly
private `2*G5` producer. The donor population prefix remains paid and live.

Relative to the old471 codes, only body states2,7,14 change: their code
changes are respectively+1,+1,-47. Hence the exact all-value current-word
change is

    Cnew-Cold = G19-47(E24+E25).                         (1)

The compiler checks the current word's complete coefficient vector and its
expansion in the actual supplied hats, including every constant shift.

## 3. Target-control word and full paid schedule

Besides J=sum E_i, use these already-paid base selectors:

    A4=E2+E6+E8+E11,
    A3=E5+E8+E9,
    D11=E18+E19,
    D14=E24+E25.

They are respectively `action_selector_126`, `prime_selector_111`,
`control_codes__duplicate_state_2`, and
`control_codes__duplicate_state_8`. Their complete vectors are recovered
from literal additions in the retained389-row base. No basis term is
supplied as a new witness or treated as free.

For target state t_i of edge i, define

    r_i=c(t_i)-1-4*[i in A4]-[i in A3]
                  -31*[i in D11]-[i in D14].

The target word is evaluated as

    Nnew=J+4A4+A3+31D11+D14+sum_i r_i E_i.              (2)

Its exact residual coefficient list is

    -1,0,10,20,0,7,16,16,7,7,10,0,17,16,7,0,0,24,
    9,0,9,2,23,1,10,2,23,5,24,6,0,13,0,23,0,23.

Equal coefficients share their selector sum. A finite compiler groups
terms using already-paid disjoint subset sums and interns identical exact
linear vectors. These are compile-time equality checks; every newly needed
binary runtime operation is emitted and counted. Signed intermediate
linear words are permitted; the supplied witnesses remain positive.

The halt code changes from63 to14. The complete target-word difference is

    Nnew-Nold = E2+E10-47E20-49E31.                    (3)

The helper checks(1) and(3) by exact expansion as well as checking the full
old/new current and target vectors from all36 actual edge labels. It guards
the literal transport rows and replaces the single comparison by

    B*Nnew = Cnew+14P.                                 (4)

The full source is reconstructed from the retained base, the new control
schedule, and the finalizer, then topologically scheduled and trimmed by
backward liveness. There is no hidden evaluation of a control word.

| Disjoint live stage | M | A | Total |
|---|---:|---:|---:|
| Retained base, including five noncontrol residual producers |142|247|389|
| Parent private control schedule |26|41|67|
| New private control schedule |22|42|64|
| Remaining finalizer rows |7|8|15|
| Complete parent |175|296|471|
| Complete successor |**171**|**297**|**468**|

Thus the net saving is four multiplications minus one extra addition,
namely three operations. The20-row finalizer includes five residual
producers already counted in the base; the disjoint ledger avoids counting
them twice. Excluding all20 finalizer rows instead gives the certificate
448=164M+284A.

## 4. Exact complete-output correction

All72 native-prefixed rows remain literal. All five noncontrol residuals,
the native/repunit product U, the height/radix and payload/source-selection
machinery have unchanged actual computed values. Nineteen of the20
finalizer rows are literal; only the control-residual producer changes.

Write r_old and r_new for the actual old/new control residuals and S for
the sum of squares of the other five residuals. Exact expansion of each
complete finalizer gives

    F_old=U*(1+S+r_old^2)-1,
    F_new=U*(1+S+r_new^2)-1.

The polynomials therefore satisfy over every commutative ring

    F_new-F_old=U*(r_new^2-r_old^2).                    (5)

The formal finalizer variables are bound to actual computed rows. U and
the other five residuals lie in the unchanged literal389-row base. The
control words themselves are expanded through actual supplied-hat leaves,
and the guarded transport rows bind those words to r_old/r_new. Equation(5)
is consequently a full-source correction, not an identity for unrelated
formal ports. No arbitrary all-value equality between F_new and F_old is
claimed.

## 5. Identical positive zeros and ordinary-input representation

At a positive integer zero of either source, its product finalizer gives
`U*(1+sum residual squares)=1`. Both factors are integers and the second is
positive. Hence U=1 and every ordinary residual is zero. Each native/repunit
factor is consequently a unit.

The pretyping and native-sign arguments in the
[computed-scale proof](residue_affine_sparse_scale538.md), adapted to h>=3
in [terminal537, Section2](residue_affine_sparse_terminal537.md), use the
native equations, positive scale, remainder equation and range information.
They do not assume the control comparison. These rows and actual ports
are all in the retained base. Thus they apply to either source before any
use of its code equation, recovering

    B dyadic, P=B^T, J=1+B+...+B^(T-1), T>=1,

and exactly one selected edge at each time row, with the unchanged prime,
action and range digits. No new assumption about a native marker or an
arbitrary numerical fixed parameter is introduced.

The words Cnew,Nnew then have canonical base-B digits c(source) and
c(target). Their digits lie in[0,41], while B>=192 is already known.
Comparison of the T+1 digits of(4) gives

    c(source_0)=0,
    c(target_j)=c(source_(j+1)) for 0<=j<T-1,
    c(target_(T-1))=14.

Injectivity translates these conditions exactly into initial loader state0,
correct successive control states and final halt state22. The old code
list is also injective and lies below B, so its old control comparison is
true on exactly the same typed edge words.

Therefore a new positive zero reconstructs the old control equality on
**the same supplied coordinates**; every other residual and U already
coincide. Recomputing the old private control schedule gives an old zero.
Conversely an old zero has the same typed chronology and satisfies(4), so
recomputing the new control rows gives a new zero. No signed or partial
inverse on witnesses is needed.

The body graph has no return to loader state0. Thus the unchanged decoded
chronology has the same paid initial doubling prefix and the same U21 body.
The inherited prefix-count, payload, terminal-bound and input proofs apply
without alteration. The resulting ordinary-positive-input universal
representation retains the original fixed recipe E=3^e. Full positive
native completeness is inherited from the parent zero-set theorem; finite
control fixtures do not replace that theorem.

## 6. Degree and finite checks

Control words remain affine in supplied selector hats, and their transport
residual has degree at most2. The native source and other residuals retain
the parent's degree bounds. The helper freshly verifies the exact main-norm
cancellation

    (X+ac+G)^2-(a^2+4a+3)c^2
      =X^2+2acX+2GX+2acG+G^2-4ac^2-3c^2.

At computed boundary degree bounds308,374,67,375 this norm has bound816
instead of the naive882. Propagating the guarded bound through the actual
new source gives native/repunit product degree at most4993 and outer SOS
degree at most98, hence complete degree at most5091. Naive propagation
would give5157. No exact-degree assertion is made.

Fresh evidence includes the complete source/count/liveness audit, all36
reconstructed edge tuples, the four entire actual-hat control vectors,
five paid target-basis vectors, exact control deltas and complete finalizer
correction. Thirty-two signed modular full-source pairs check the computed
base and(5). Another236 finite edge words, including36 accepted control
words covering every edge, compare old/new code equations against actual
adjacency at bases192 and256, giving944 checks. These are control words,
not claims of accepted payload histories or full native Pell zeros. No
huge historical fixture is executed.

The bounded search that suggested this plan is not the proof and is not
claimed exhaustive over code assignments. Only the emitted selected valid
plan is certified here.

## 7. Frozen provenance and replay

| Inert dependency | SHA-256 |
|---|---|
| `residue_affine_sparse_shared471.py` | `8940d9c5b008bbe9d6ea210d938634afec1e59a76362b2c3a4aa25c53d460246` |
| `residue_affine_sparse_shared471.json` | `4732844a06fb9285d9fc57aa8dcd220e3664f965ec850393c830d2a453832ced` |
| `residue_affine_sparse_shared471.md` | `12c4725b79fe4e9173bef944100e41612b20e213f13b8f470d34802d6c5839c4` |
| `residue_affine_sparse_factored.json` | `39e52871ae5137f8edd111055e6338db4bf17b232d145a24390b1675d8c99fda` |
| `residue_affine_sparse_factored.md` | `b169236c449623049759b7ac0877b2202b3aba389ace8e06d31370396abb9ea7` |
| `residue_affine_sparse_control_codes.json` | `2f9e97873bf4b02da0e6664bdf1ac150d4b3f5befb2bb5ae907c01c3c1dc7d9d` |
| `residue_affine_sparse_control_codes.md` | `be133b5d93c082c3f3022e4b9990140ff3de71cf7202a7ba281a48e8c77d34da` |
| `residue_affine_sparse_terminal537.md` | `9deba23f3b210d730fd32a2a10aa886edc9637c4f8d26010cc0f0f55a7c7f6d1` |
| `residue_affine_sparse_scale538.md` | `0c6e6bd9606a6c6b1c70f21575784ac24ed9ff2f64ab788cc6c64b0106979623` |

New helper SHA-256:
`4b73c18e91473205dfb50edaf3e289898af305b14781ca1e10ce8a2ec06d834f`.
New receipt SHA-256:
`1aa26a73ebce4e5a8cfeb443b7d2aa296bbf7816a5c842728f6a3862872936b4`.

Fresh generation and fresh normal/optimized exact receipt replays from `/`
pass. The helper rejects duplicate/noninteger/nonfinite JSON, preserves
exact operand types, binds its bytes into the receipt, and keeps all guards
active under optimized Python. Output creation is exclusive.

```sh
u21_wip=/absolute/path/to/native-stream-queue
python3 "$u21_wip/residue_affine_sparse_recoded468.py" \
  --root "$u21_wip" --expect "$u21_wip/residue_affine_sparse_recoded468.json"
python3 -O "$u21_wip/residue_affine_sparse_recoded468.py" \
  --root "$u21_wip" --expect "$u21_wip/residue_affine_sparse_recoded468.json"
```

Only this one-program coupled-product array is emitted. No two-program
transfer, other historical finalizer/plan, circuit minimum or universal
count below84 is asserted. No repository or frozen predecessor file was
modified.
