# Independent review: finite eager Tree root projection

**PASS; no correction requested.** I read the complete frozen author source and note, the occurrence-flow parent source and proof, and the relevant corrected eager Tree kernel. Independently reconstructed complete polynomial identities, gate ledgers, natural zero maps and public boundary checks support the stated result. The external row count remains part of the construction.

The reviewed [author source](eager_tree_root_projection.py), [receipt](eager_tree_root_projection.json), and [note](eager_tree_root_projection.md) are authenticated before use. This independent [checker](review_eager_tree_root_projection.py) and [receipt](review_eager_tree_root_projection.json) pin that trio, the three occurrence-flow artifacts, and the actual corrected kernel. No historical suite or full author `verify` suite is replayed. Public source construction and bounded map checks execute authenticated source bytes, without loading bytecode caches.

## Natural-domain theorem

At a parent natural zero, pointer row sums and tags force the usual zero/one premise selections. Incoming occurrence balance implies that every root-reachable row has positive mass and that no root-reachable directed cycle exists. This inherited graph theorem is used with exactly its natural-coordinate hypotheses.

Retain the root-reachable rows, replace every other row by the valid leaf dummy, and recompute occurrence counts from one root injection. No retained row points outside the reachable set. An edge into row zero from a reachable row would create a reachable cycle, including the self-loop case, and is therefore absent. Dummy rows have no outgoing pointers. Hence all `p[j,s,0]` are zero and the new root mass is exactly one. Repeated premise slots contribute with multiplicity to occurrence counts; they do not alter the acyclicity argument.

The author's algorithm implements this normalization: its topological indegrees count distinct adjacent rows, while propagation uses the full slot multiplicity. My checker uses a separate DFS postorder implementation and agrees on the constructed zeros. The dummy's decomposition fields `d=e=q=2,j=4,k=8` are the literal pairing values for its zero decomposition fields and code `(x,y,z)=(0,0,1)`.

Substituting `mu_0=1` and every incoming root pointer zero makes the root balance identically zero on all scalar assignments. Every other residual is retained with this substitution. Thus restoring constants gives a bijection between child natural zeros and the **normalized parent slice**, with the same external coordinates and the same N. The normalization above proves equality of represented triples with the entire parent at each N. It does not imply a bijection with all parent witnesses, a direct projection of every parent zero, or uniqueness of a normalized certificate.

Signed evaluation and rational coefficient checks establish algebraic identities only. The graph semantics require natural integers, including zero. No fixed-arity universal polynomial, ordinary-input loader or numerical universal operation bound is supplied.

## Entire emitted source and fair counts

For all 16 saved forms (`N=1,...,8`, both cleanup modes), the checker builds the actual parent and child source, independently expands every residual into a multivariate coefficient dictionary, and checks all 1,688 retained residual identities. It verifies that the deleted root balance has the zero polynomial after substitution. It independently rebuilds the literal full SOS tail and proves all 16 complete polynomial identities, without using the author's expansion or folding functions.

Every emitted source gate and free coordinate is live. Exact type, closure, acyclicity and complete ledgers are independently checked. For the default schedule, every parent instruction outside the original fixed-coordinate dependency cone remains literally present and unchanged. This verifies that unrelated static simplifications are not silently credited to the projection. The optional cleanup removes exactly N further additions; both full polynomials remain identical on the same substitution graph.

The retained `d_0-F(a_0,b_0)` residual has quadratic homogeneous part `-(a_0+b_0)^2`. Every residual has degree at most two, and the sum of real squares of their highest-degree parts cannot cancel. Thus exact degree four holds for all N, in both schedules. The checker also obtains degree four by full coefficient expansion on all 16 emitted forms.

General interface:

```
witnesses = 3N^2+16N-1,
residuals = 23N+2.
```

For `N>=2`, the default complete source has

```
M = 12N^2+41N+5,
A = 15N^2+53N+4,
total = 27N^2+94N+9.
```

Relative to the literal flow parent, the reductions are `15N-2` multiplications and `15N+2` additions. The root balance deletes `3N` products and `3N+1` additions; root-column lookups delete `9N` products and `9N` sum additions; pointer row sums delete `3N` additions; fixing root mass deletes `3(N-1)` additional flow products; and the finalizer deletes one square and one addition. These categories are disjoint. The optional static cleanup saves N additional additions.

At `N=1`, the multiplication formula still gives 58, but single-entry lookup and pointer sums supply none of the corresponding addition savings. The exact counts are `58M+84A=142`, or 141 with static cleanup. The parent has 160 operations, so the default saving is 18, not the general `30N`. The published table agrees with every literal emitted ledger; the 16 full sources contain 17,916 live paid gates in total.

## Independent zero and counterexample fixtures

A separate bounded eager-application interpreter and row constructor supplies ten genuine applications covering all five root rule types. Padding each by zero, one and two rows and checking both cleanup schedules gives 60 complete normalized-zero map checks. Each verifies the parent polynomial, child polynomial, independent occurrence counts, constant restoration and both directions of the normalized-slice inverse.

I also constructed a six-row parent zero independently from the actual `(10,1014)->1014` application plus a disconnected omega counterfeit. The counterfeit has two slots into the genuine root and one self-loop. With circulation `c`, masses at the root and its three leaves are `1+2c`, the counterfeit mass is c, and a dummy row has mass zero. For `c=1,2,5` these are actual parent zeros. Directly dropping the prescribed coordinates produces a nonzero child; for `c=1`, its value is exactly the reported `4112998` in both schedules. Independent normalization gives reachable set `{0,1,2,3}` and masses `[1,1,1,1,0,0]`, replaces the other rows and yields zero. These six checks demonstrate the precise failure of an unrestricted coordinate projection.

Eighty rational, signed whole-source evaluations supplement the full coefficient identities. They make no claim about computation outside the natural domain.

## Guard and provenance boundary

The public `build`, `checked`, `evaluate`, `restore`, `project_normalized_zero` and `normalize_parent_zero` paths reconstruct canonical packets. The independent checks include 62 rejected malformed calls, exact Boolean/integer/container distinctions, complete coordinate sets, negative default-domain values, nonzero parent tuples and actual nonnormalized parent zeros. Four mutation/copy checks confirm that a caller cannot alter another emitted packet. The source also rejects optimized Python.

Every public build authenticates the executable parent and actual kernel before loading source bytes. Two warmed source mutations are rejected. A preloaded fake kernel module is overridden by authenticated source, and the exact preexisting module object is restored afterward. The parent receipt and note are authenticated by the author's `verify` entry point, **not on every public build**. Two focused mutation checks confirm this distinction: builds remain unchanged while `verify` immediately rejects the companion mismatch. The note does not promise a stronger companion-pin boundary.

The independent checker does not exercise unrelated historical APIs or claim a general hostile-interpreter security boundary. It tests the advertised canonical packet and assignment contracts.

## Replay

```
python review_eager_tree_root_projection.py \
  --repo /path/to/Proofs \
  --root /path/to/occurrence-flow/parent/trio \
  --subject-root /path/to/root-projection/author/trio \
  --expect review_eager_tree_root_projection.json
```

`--output FILE` writes the deterministic receipt. Its source hash and every authenticated input pin are recorded in the receipt. The checker uses only the standard library and creates temporary pin-mutation fixtures outside the repository.
