# Released replay record

The original CODE ONLY / HOLD preparation was committed as cb0046130a.
Its final inventory hash is
`0e37ccc2545afbdac0278b91509febd254aa8f00912eab50ee379290a5dbc1c9`.
The full root static review and independent peer review completed before
the first application execution. The only pre-release portability change
added empty verification/.gitkeep and its HOLD entry; all original27
preparation payloads were preserved. Core/pins were then unchanged:

| File | SHA256 |
| --- | --- |
| build.py | `cc2088544ad7f54188e6e843f77f9c5ff17aa4e591c1631f42242f0750641956` |
| check.py | `39a21d67551ebffa0f5382989744b912f7000a8f99dfcc2681a8a1d597cf5983` |
| SOURCE_PINS.json | `dd163fdcf2cead8ccf929de654bd133711013a9a4f50f6f0410aec043966cd7a` |

Root explicitly released exactly the following five commands. They ran
sequentially from this directory, all exiting0 on the first attempt:

```sh
python -B build.py --output BUILD.json > verification/build.txt
python -B check.py --output CHECK.json > verification/check-normal.txt
python -B -O check.py --output CHECK_OPTIMIZED.json > verification/check-optimized.txt
python -B build.py --check --output BUILD_VERIFY.json > verification/rebuild-normal.txt
python -B -O build.py --check --output BUILD_VERIFY_OPTIMIZED.json > verification/rebuild-optimized.txt
```

Every whole JSON receipt equals its whole stdout file. Their hashes, in
that command order, are:

1. `f4f90a0d20667c4d102551aa9b60df234d6e2ea8698c88aa2482b34f7f677666`
2. `a1062b7a9244b85031e7571d04e45344e4523d0d1d99985755f2a6d08f1124e6`
3. `049fd46dbcb1208c11b4ec0bc79992f2e49c14f5fc75d58a5ab1c7ad3ff1fedb`
4. `5ed0e1668b0d4f5020d85b37504990fdb49c284c7dc69dd19ff38cf8450edb96`
5. `d3668d52cadb82ff6e4010b34d18eb58d9d24e88210bd418a03ef455ef7a0b91`

No failure, patch, retry, extra application command, optimizer, incoming
main, source compiler, TeX/renderer or Lean execution occurred. Inert
hash/JSON/byte comparisons and separate metadata preparation followed.
The complete eight data artifacts became immutable after materialization;
INDEX is
`5e676c161a37e1ec42abcff8b320fd74f6b8be84d711ded59eb0e34c62dca6a6`.

Root then ran fresh normal/optimized checkers and normal/optimized pure
rebuilds outside the author packet. Root reported all four exit0 and all
eight whole JSON/stdout files byte-identical to the corresponding author
records. The author did not copy or rewrite root records. Root explicitly
authorized closing the author manifest after these comparisons and did
not authorize or request another application run.

AUTHOR_RUNS.json pins full commands, exit codes, whole receipts/stdout,
static approvals, immutable preparation and generated data. RESULTS.json
and RESULTS.md record the actual four operation/degree pairs, complete
leading-form term counts, controls and exact direct calibration scope.
SOURCE_PINS remains the original184-file/six-core/seven-closed ledger.
Positive completeness still requires the complete canonical family with
R>3q, q³|Y and fresh positive witnesses. These finite runs do not replace
the sealed unbounded V²/general bV/native theorems or promote a page.
