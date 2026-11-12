# Frozen current comparison sources

These are unchanged comparison sources and package claims copied from the
inspected incoming archives, not proposed implementations of the new G rule.
`../../evidence/comparison_sources.json` gives each archive identity, exact
archive member, SHA-256, interface contract and locally reproduced measurement.
The final comparison boundary is repository commit
`2a724ea8ec6665f91aa74c892414584b36ca698d`.

All measurements use the complete module after CPython 3.12.14
`ast.unparse(ast.parse(source))` plus one LF. Gzip uses level 9 and timestamp
zero and is informational. The imported packages' original claims and metrics
remain beside these files, named by their source package.

| Source | Significant tokens | AST nodes | Normalized bytes | gzip-9 |
| --- | ---: | ---: | ---: | ---: |
| `checker_bytes.py` | 263 | 303 | 520 | 329 |
| `checker_tokens.py` | 256 | 283 | 594 | 346 |
| `checker_ast.py` | 260 | 278 | 602 | 344 |
| `previous_521_bytes.py` | 263 | 300 | 521 | 327 |
| `native_goal_checked.py` | 358 | 413 | 788 | 460 |
| `guarded_goal_checked.py` | 407 | 459 | 921 | 507 |
| `native_typed_full.py` | 401 | 468 | 897 | 505 |
| `native_typed_eqd.py` | 390 | 454 | 878 | 498 |
| `one_sided_c7_checker.py` | 1171 | 1339 | 3246 | 996 |
| `one_sided_m7_control.py` | 1196 | 1364 | 3302 | 1005 |
| `upstream_one_context_checker.py` | 1089 | 1150 | 3358 | 990 |

The compact coordinate envelope is **256 tokens / 278 AST nodes / 520 bytes**
across three different programs. These compact sources assume a canonical
guarded public goal and omit an included public-goal validator. They must not
be compared unqualifiedly with full Eq/Q/D, goal-validating or fully typed
interfaces.

`native_goal_checked.py` validates a full native Eq/D public goal, with Q
available internally. It does not impose exact integer/list typing on every
certificate field. The two `native_typed_*` files have that stronger type
contract, and the `full` file admits all Eq/Q/D public formulas.

The earlier upstream one-context source is copied exactly. This package's
`../one_context_seven.py` is a derived matched control: it replaces its two
introductions by the existing witness-sensitive introduction and is otherwise
unchanged. `../../evidence/one_context_seven_origin.diff` records the exact
change. The seven-rule control is not represented as an exact archived file.

The parent `../LICENSE` covers inherited ProveIt material. Source hashes and
size metrics were checked here; the imported packages' entire process-test
suites were not rerun for this comparison.
