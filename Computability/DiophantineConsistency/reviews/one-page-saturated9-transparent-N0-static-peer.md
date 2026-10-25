# Independent shared-cut audit and transparent-N0 static review

Reviewer: `/root/intake_e13`. Date: 2026-10-24. **Static approval; no unresolved finding.** I read the full new code/prose/pin diff, all changed historical notes and the full v6 failure transcript, and independently inspected every named cut in the literal DAG. I used inert JSON/file/hash/dependency inspection, not the new auditor, renderer, parent/source program or Lean. No corrected module was imported, compiled or executed by me. The actual complete mathematical audit, controls and rebuilds remain pending release.

## Exact correction and its ordinary justification

Current auditor SHA-256 is `83bee8007521b3ad79c1e1bf066089e4b506fdf6c3254e8ea909307d3bd86650` (761lines). I verified whole-file equality to reviewed/archived v6 after the sole replacement of the two unconditional atom assignments by:

    # N0 is also a shared B-power helper in later source chains.
    replacement = value if name == 'N0' else atom(name)
    printed[name] = replacement
    context[node] = replacement

This occurs only **after** complete RHS parsing, correct ordered alias/node binding and exact equality with the actual DAG block. At the N0 stage the checked value is the monomial B^117. Reusing that proved polynomial in both environments is ordinary substitution of an established identity over the same free coefficient ring. It supplies no assumed relation, numerical test or unquantified port. Every other cut remains atomic, and exact identities, parser full consumption, touched-node coverage and all controls remain unchanged.

The original context design lost a required dependency: node55=B^117 is also used as an internal power helper in Z, while printed Z is expressed in B alone. Direct consumers of55 are exactly nodes56,127,142,166,369. In particular142=55*72; the target Horner chain reaches it before163. Making55 an independent N0 atom therefore produces a false negative at Z. The corrected proof retains the valid relation instead of trying to compare polynomials under a false independence assumption. I did not catch this shared-helper issue in my initial static approval; the actual failure and old reviewed bytes are preserved.

## All-forty-cut dependency audit

I matched all40 ledger node records to the literal unchanged graph and compared each actual cut's earlier-cut/input dependency set with the actual printed definition, treating N0 transparently and retaining the already reviewed exact374=R+1 bridge. Fixed coefficient leaves/scales are separately pinned and are omitted from the dependency-set notation below. B is atomic after its definition.

| Checked cut/node | Actual preceding cuts or inputs needed |
| --- | --- |
| B/13 | b |
| N0/55 | B |
| ell/107 | B |
| Z/163 | B |
| u/186 | ell,g |
| Gc/366 | B,u |
| Sc/370 | B,Gc,Z,g |
| Tc/167 | B,Z,b,ell |
| Lc/51 | B,b |
| R/375 | Lc,Sc,Tc |
| N/377 | B |
| cap/401 | B,b |
| U/382 | N,w |
| Y/380 | N,s |
| M/381 | R,Y |
| P/396 | M,U |
| k/399 | P,R,h |
| A/384 | M,U |
| B1/432 | R |
| W1/3 | b,w |
| Jr/388 | A |
| Qr/10 | C,W1 |
| m/411 | C,Y,cap,g,k |
| Omega/412 | Jr,m |
| E0/393 | Jr,Qr,W1,n |
| V0/413 | P,k |
| delta/415 | A |
| D/418 | C,delta |
| e/421 | C,Jr,i |
| de/422 | D,e |
| Fp/425 | de,delta,e |
| Lambda/428 | A,C,D |
| Gp/430 | A,Fp,Lambda |
| H/438 | B1,C,Fp,j |
| Tm/440 | A,de |
| V1/441 | Gp,H,Tm |
| I/452 | Gp,H |
| a0/448 | V0,k |
| a1/454 | D,Fp,I |
| Theta/444 | E0,Omega,V0,V1 |

The final boxed tail needs exactly Omega,Theta,a0,a1. The union of these literal traversals touches all464 nodes. Every dependency set matches the printed expression after N0=B^117 substitution. No additional unprinted atomic-cut reuse was found. Other shared partial products are safe: node383=M*U is not an atomic cut when A/P reuse it; node378=N² remains a shared expression for U/Y; node439=Gp*H remains available to V1/I. They do not require an extra relation between two independent named cuts. The one R+1 bridge is already bound to the exact375=374−1 row.

Thus the N0-only exception suffices for the identified cut-dependence problem across this whole graph; no broad transparency rewrite is justified. This structural/ordinary conclusion does not claim that an unexecuted complete auditor or its later PDF checks have passed.

## Frozen closure and unchanged rendered mathematics

Current TOOL_PINS `3294a513f56eb8ab26e0d1afe943b3dddc307b05a8ea204b863094363d5ded4d` passes all56 external/119 preparation-history-render/four core records, with every hash and byte count. SOURCE_PINS `349e7a590bf5e493629665bf79ec19227c8bf9733452da769c979dd9d4526e24` passes all51 external/five core records. Final proof hash is `1eecf6a3aee2bbd7f0b2ec52756b7521bf3a974526aa48c7041233a94cd05e53`; toolchain hash is `f52d616548a7bef9c870676ddacfaeca0759e61c19b979341670d669a7628b51`.

All six complete historical inventories pass exact names/hashes/bytes: v1..v4 have13payloads each, v5/v6 have21each. The new v6 manifest is `41829b2659aa43cc9668f5c4d26e28e1b2fed18e902ef526abe27fb99e109587`; it preserves complete old core/pins, successful render files and failed-Z trace. It does not relabel any failed mathematical audit as success.

TeX `e8a590cd71859fdddbd749ddc656b2507187cdae49990fa40de5db0875f8abef`, graph, formula map, renderer and all five live derived render files are entirely byte-identical to v6. Actual PDF remains `4ae1bdee9aa57c074f14f0790823791724c6032baca42e4b724245476ea554d7`. My separate visual PASS `c9b0a606ec50e920e3c78e77478442f53a3fb7066380753ddd74efac8e8b310b` therefore continues to concern these exact PDF/TeX bytes; it is not a mathematical-auditor result.

Root may decide whether to release the same five commands against this checkpoint. Complete universal block/kernel identities, whole tuple/eleven-leaf reconstruction, all29 actual-TeX corruption controls, both auditor modes, both deterministic rebuilds and independent replays must still pass. Canonical/source/ordinary parent/Lean artifacts remain unchanged.
