# Proposed selected fresh checks (not executed)

Use a fresh writable copy of Source154. Run Python normally with assertions enabled and a separate60-second wall cap per command; capture argv, return code, elapsed time, stdout/stderr and newly written receipt. No package installation is needed.

From `research/theory/`:

```sh
python3 -B check_mp_conventions.py
python3 -B check_membership_blind_detachment.py
python3 -B check_shifted_even_codec.py
python3 -B check_negative_atoms_core_matrix.py
python3 -B check_t_template.py
```

These establish, respectively, finite symbolic-stack compiler identities, bounded inverse-decoder/model regressions, bounded shifted-codec arithmetic, exhaustive finite-value fiber identities, and a Boolean identity for the literal two-time template. None establishes an infinite-model theorem or machine runtime by finite testing alone.

Optional baseline-overlap check, supply the literal accepted K219 source file:

```sh
python3 -B check_boot_permutations.py --sites /path/to/sites219.json
```

Optional literal-source audit, from `research/encoding/theory_audit/`:

```sh
python3 -B audit_t_native.py --codes222 Codes222.v --codes230 Codes230.v --kcode230 KCode230.v --thm222 Thm222.v --enum222 Enum222.v --receipt fresh-native-ast.json
```

This parses the native definitions and full rule list as text; it does not invoke Coq. It is not a proof of the countermodel.

Do not invoke `portable/reproduce.py`: it performs manifest validation and recursively replays ancestor work before the leaves. Do not rerun the baseline219 or no-push-copy universal runtime. Root owns any cache-on217 construction/search/runtime separately.
