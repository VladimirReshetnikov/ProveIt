# Literal source contract for MP-first, reset, no-dummy Variant B

## Result

`mp_first_from201.json` has **202 live source nodes**, maximum zero-run 7,
maximum path length 35, and 6,440 leaf sites. The closed reassociation search
found an equivalent 202-node version of path length 34 in
`mp_first_rotated_best.json`. The ordinary Wade backend emits 264 working
states from the first DAG. These are **not** sub-246 results.

The input is the independently audited source-201 program at
`context_folds/recovered/67/research/root_search/rebracket201_minimal.json`,
SHA-256 `5093d32f7e62a0d7e5a0632b8d969b0110fec4a301da85e581b2afd5a61a3dbe`,
recovered from the pinned ProveIt commit
`7ba1598461c6e485c5aeb8f673c0b1d571f8012b`.

## Exact edit

Retain all original nodes other than:

- 189 becomes `((N,166),(N,187))`.
- 197 becomes `((N,169),(N,204))`.
- Add 204 as `((N,41),(N,205))`.
- Add 205 as `((I,5),(N,186))`.
- Garbage collection removes the now unused node 188.

Node numbers refer to the preserved source-201 numbering, not Wade's
renumbered binary output. The literal generator asserts the old node shapes
before editing them.

## Registers and inherited helper contracts

The logical registers, in order, are N,T,S,A,D,H,X,Y,L. The scheduler N,A,L,
the theory emitter, all constructors, and all selector decisions are unchanged.
The existing helper contracts used by the edit are:

1. Node 166 consumes H and changes no other register: its body is
   `while H>0: H--`.
2. Node 51 unpairs S into X and Y and restores Y into S. With X=Y=0 it
   returns X=head(S_old), S=tail(S_old), Y=0.
3. Node 46 transfers X into H, consuming X. Thus node187=(51,46) is an
   **additive** pop into H; it is not an overwrite if H was nonzero.
4. Node 41 consumes D, incrementing both T and X once per unit. Its literal
   nodes are 41=(D4,N40), 40=(I1,N1), 1=(I6,C3). With T=X=0 it returns
   D=0, T=X=D_old. The loop has decreasing variant D.
5. Node 169 is the inherited destructive comparison of X and H. It consumes
   both, returns normally iff their old values agree, and returns one outward
   break otherwise. Node186=(169,Halt) therefore halts iff they agree and
   otherwise returns normally with X=H=0.

The structured semantics consumes a break only at the enclosing *left*
branch, and consumes a continue only at the enclosing *right* branch. These
are precisely the semantics used by the inherited source proof and by the
independent diagnostic interpreter. No Python arithmetic shortcut is used in
that interpreter.

## NIP contract, all natural values

Node189 now clears H before calling the additive pop. Assuming X=Y=0, it
returns

    (T,S,D,H,X,Y) -> (T, tail(S), D, head(S), 0,0)

for every natural T,S,D,H. The two constituent loops terminate on H and the
inherited unpairing measure. It never halts. Clearing H is essential: the
initial rejected edit that called187 directly returned H_old+head(S), which
is not the desired command and has no established soundness invariant.

## Successful MP contract, all natural targets

The unchanged source MP prefix constructs I(T,D)=4P(T,D), compares it with H,
and leaves T=X=H=0 on success; D and S are preserved at this boundary. Failure
exits before the new suffix and still returns T=H=X=Y=0, preserving D and S.

On success, node204 first copies and consumes D using node41, leaving
T=X=D_old and D=H=0. Node205 sets H=1 and runs node186. Hence it:

- halts iff D_old=1;
- otherwise returns T=D_old, D=H=X=Y=0;
- never changes S and thus performs no dummy truth push.

This proves the local command contract for all natural values from the stated
scratch-register interface; the proof does not extrapolate a finite test.
The arithmetic and control claims above can each be expanded into elementary
induction in PA, hence in ZFC, using the inherited helper contracts.

## Composition and remaining obligations

These local contracts instantiate the abstract Variant B proved in
`logical_routes/mp_first_f_proof.md`: soundness, a complete derivation compiler,
and safe starts including the prefix246 logical tuple N=3,D=3,T=S=H=0.
The original theorem calibrating the native calculus to ZFC supplies the
logical equivalence. A complete end-to-end theorem for a newly emitted binary
machine still needs the matching compiler and blank-tape initialization
simulation. The Wade table emitted here is only a cost/control measurement;
it is not claimed as the requested ZFC-calibrated small machine.

## Reproduction and diagnostics

Run `python research_sub246/machine_encoding/mp_first_from201.py`.
It independently checks 490 full MP cases and 936 NIP cases, compiles a
complete binary table, and re-extracts every emitted source edge. The finite
checks are regression tests, separate from the all-natural local argument.

Run `python research_sub246/machine_encoding/rotate_variants.py --iterations 10000`
for the recorded 50,000 safe-associativity proposals. Every improved source
is checked for identical complete ordered normal form and exact guarded
leaf-transition graph, not merely tested on a finite register sample.
