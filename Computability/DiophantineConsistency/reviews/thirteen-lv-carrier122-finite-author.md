# Two mixed-carrier profiles: finite author audit

Author: `/root/controller_certificate`, 26 October 2026. This is author
validation of the new finite auditor, graphs, coefficient copies and README,
not an independent review of my own code. I also authored the preceding
corrected-strong auditor and correction module. `/root/circuit_reduction`
separately authored the new Lean witness maps, focused checks and ordinary
proof. I read those complete frozen sources but did not compile Lean for this
packet. Root review is separate from both authors' checks.

All paths below are relative to `Computability/DiophantineConsistency`.
No maintained equation, accepted parent, shared object, shared status document
or Git state was changed in this work.

## Frozen artifacts and execution

The new packet is `research/thirteen-lv-carrier122/`.

| File | Bytes | SHA-256 |
|---|---:|---|
| audit.py | 23896 | `38a8647f2f3851aa67756b6499af5c4c359a69b883358e12b6f4fbe368920ba2` |
| polynomial72.json | 7752 | `2ac2f00f08146d61b8d98c15b3f844b0ae00330eba825f80629d0a1e48e27045` |
| polynomial.json | 7901 | `b701b3c9e56f26069c69ed5ba495e2beae952d88d8c1fe2b94df0d88b1e3c09a` |
| CERTIFICATE.json | 155528 | `3b4e66705173eac73939971d166b5db70be467eb85b2ef7d1dde232ed799d118` |
| README.md | 10081 | `460d3dcd429a8f80455bccd741c58c3dc1a1600abb5bb50849081456cc66a6cf` |

The pinned separately authored Lean main/check and ordinary proof hashes are
`d64e31b377007ddd05964e29a1976c857d036d6eb919524df58c3bd8c237bd02`,
`3a4301d7b4c72dbf52dc365521397219b929159a23657eaa63d6f9470ba51bdf`, and
`0b4652adbdb5938ba52bf0865799acdc19dcbc13e23948ce16dc33c83cfd8386`.
These are data bindings in the finite auditor, not a substitute for Lean
checking. The separate Lean author receipt is
`reviews/thirteen-lv-carrier-lean-author.md`, SHA
`369835103c933b0a04d569093d8e543d4b1d0df5d2154cfbbb0836e377308729`.
Its two fresh leaves and reused prerequisite inventory are explicitly distinct
from a fresh full native/machine dependency closure.

After reading the complete frozen predecessor auditor and both parent graphs,
I read every new verifier line and every subsequent edit before executing:

```sh
python3 -B Computability/DiophantineConsistency/research/thirteen-lv-carrier122/audit.py --write
python3 -B Computability/DiophantineConsistency/research/thirteen-lv-carrier122/audit.py
python3 -B -O Computability/DiophantineConsistency/research/thirteen-lv-carrier122/audit.py
```

All three first attempts exited zero. Normal and optimized checks reproduced
the exact same complete graph and certificate bytes. The auditor imports only
Python's standard library; it does not execute/import any predecessor auditor,
native certificate script, machine decoder or archive code. All gates use
explicit exceptions, so `-O` does not remove checks. Default mode is read-only;
`--write` only materializes the owned two graphs, four gzip copies and certificate.
I also read both entire materialized instruction schedules and the final README.
There was no failed finite execution to hide or reinterpret.

## Whole graph, witness identity and exact degree

Both graphs use precisely the thirteen positive coordinates
`J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma` and the four fixed ports
`beta,K0,MC,MF`. The last port is the source mask already shifted by beta once.
The existing `cTminusR` row computes `L=c*T-R`. The only carrier change inserts
`LV=L*V` and replaces `LB=V2*G` by `LB=LV*G`. `V2=V*V` remains live in the
auxiliary factor. The independent parent transformations produce:

| Profile | Multiplications | Additions | Subtractions | Live gates | Exact degree |
|---|---:|---:|---:|---:|---:|
| uncorrected | 41 | 16 | 15 | 72 | 124 |
| corrected | 41 | 17 | 16 | 74 | 122 |

Every gate, all thirteen coordinates and all four ports are reachable from
each output. Exact modular evaluations additionally prove nonconstant
dependence on each coordinate at the actual fixed ports, and on every formal
port with the other ports fixed. They are not zero-set tests.

The graph is evaluated over nine independent common polynomial cuts, after
checking that all corresponding actual subexpressions are independent of m.
For `d=G*(V^2-L*V)`, evaluation of the whole old graph at `m_new+d` equals the
whole new graph at `m_new`; the inverse substitution is checked independently.
The maps compose to identity. The complete nonzero same-coordinate difference
is also calculated: the old and new polynomials are not falsely identified.
The corrected-versus-uncorrected residual identity is checked on the whole
product, and stripping the two correction rows reproduces exactly the full
72-row schedule. Independent polynomial negative controls reject both the
old V-squared carrier and a reversed witness-map sign.

Complete homogeneous leading polynomials are propagated through every row,
with coefficient ports assigned degree zero. The only complete leading
cancellations are the main norm in both profiles and the corrected strong
coefficient in the 74 profile. They are resolved by full 323-term and 353-term
polynomial expansions and independent algebraic identities. No unresolved
cancellation is replaced by an assumed degree.

Writing `q0=beta*J`, `k0=eta+zeta`, `C0=q0-F-alpha`, the factor degrees are
22,18,48,36 for the 72 profile, and 22,18,48,34 for the 74 profile. The complete
leaders are respectively

```text
-128*q0^69*gamma*i^2*k0^11*w^10*s^19*f^6*T^4*C0^2
-256*q0^68*gamma*i^2*k0^11*w^9*s^19*f^6*T^4*C0^2.
```

Each expands to 72 terms. Selected coefficients are exactly
`-128*beta^71` and `-256*beta^70`, so the actual positive beta preserves the
claimed exact degrees. This finite polynomial calculation is not advertised
as a Lean `totalDegree` theorem. Positivity of the subtractive witness map is
proved in the separately authored Lean/ordinary proof from each actual zero;
the finite ring identities alone do not prove it.

## Entire coefficient values

The auditor reconstructs all four complete integers from all 3297 entries of
the pinned doubled coefficient array and the literal current2011 geometric
recipes. It checks full integer equality with every decompressed gzip payload,
all four native certificate port records and scalar boxes. It does not merely compare
hashes. The normalized 71-row parent's old2471 ports are explicitly replaced
with this same actual2011 tuple, rather than asserting equality of distinct
specializations.

| Port | Bits | Raw bytes | Raw SHA-256 |
|---|---:|---:|---|
| beta | 94517 | 11815 | `a22ea3808ae016284c057d90f1bf2b76db1be2d34d11c0856f3315f6577d4b27` |
| K | 94941 | 11868 | `64a62b9e1eb8642492a159fc5c3a2e1c131a99c0e2f1e3b8b90fac9241166ec7` |
| MC | 94517 | 11815 | `2b5c9296e32616260e64a051c92892645b9aa1bf0bf4c0d931e464080702ca9f` |
| MF_source | 94518 | 11815 | `5c15fc24e4978b878ed531abf30b2dcfe255083372034612b759b65eee1f0c25` |

Total raw size is unchanged at 47313 bytes; the four included gzip payloads
total 4230 bytes. All complete formula data remain present. Graph negative
controls also reject missing c-squared/LV rows, a rational leaf, an extra
coordinate, a wrong output, changed port metadata and the wrong correction sign.

## Provenance and limits

The mixed product already appears in
`research/scaled-auxiliary118/THIRTEEN_VARIABLE_LEAD.md`, SHA
`7c332d1ff88f9b2885c871ef846ad9dba0462e68a0fec0541b86ffd5a0539191`.
That fully read note credits the inert archive companion and predicts an older
unnormalized profile. I did not execute the archive. This packet completes
the current positive-zero maps and materializes the two full current-port
profiles; it makes no novelty claim for the underlying mixed product.

The 72/124 profile improves both recorded metrics over the accepted 73/126
checkpoint. The 74/122 profile provides a different degree/count tradeoff;
neither is a global minimum. The maintained 14/65/150 page is unchanged.
The external Lean consistency endpoints, finite degree calculations and this
receipt do not establish an HA derivation, an internal ZFC proof, actual
consistency, or actual unsolvability.
