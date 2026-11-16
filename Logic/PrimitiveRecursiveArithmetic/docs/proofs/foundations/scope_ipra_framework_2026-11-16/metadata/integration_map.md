# Integration map

| SCOPE layer | Existing ProveIt component | New implementation target |
|---|---|---|
| Object judgment | `ConciseIPRA.Prf PRAAx` | no replacement |
| Structural composition | `Prf.subst`, `weaken`, `trans`, `exE` | `Framework/SCOPE/StructuralKernel.lean` |
| Fixed term abstraction | `PTm.toPR`, `toPR_eq` | reused directly |
| QF induction | `PRA.qfInd`, `IPRA.ind` | trace and fold packages |
| Equality bit | `eqb`, `eqb_of_eq`, `eqb_of_ne` | Boolean compiler atoms |
| Least bounded search | `Search.mu`, `search_found`, `search_minimal` | accepted-bit adapter |
| Finite folds | `recDef`, sums/products | arbitrary-arity Boolean folds |
| Codes | pairing, division, multi-sums/products | mixed-radix certificate module |
| Cyclic resources | prior FINER human theorem | checked demand-closure module |
| Relational witnesses | prior viability frameworks | checked backward viability module |
| Stable outputs | prior stable-observer/SCR ideas | exact/quotient/metric/gap interfaces |
| Backend transport | `IPRABridge` open/scoped APIs | thin adapters only |
| Application migration | theorem packets and clients | four staged pilots |

The ordinary `Prf PRAAx` layer remains canonical. Native scalar calculi and
Foundation arithmetic are export backends, not parallel places to redevelop
the general mathematics.
