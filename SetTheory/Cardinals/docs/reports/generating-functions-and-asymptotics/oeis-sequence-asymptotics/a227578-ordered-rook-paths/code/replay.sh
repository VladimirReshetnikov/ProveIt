#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
ROOT="$PWD"
PYTHON="${PYTHON:-python3}"
"$PYTHON" code/verify_manifest.py
"$PYTHON" - <<'PY'
import sympy, mpmath
assert sympy.__version__ == '1.14.0', sympy.__version__
assert mpmath.__version__ == '1.3.0', mpmath.__version__
PY
mkdir -p .replay
cd .replay
run() { printf 'Running %s\n' "$1"; "$PYTHON" "$ROOT/code/$1" > "${1%.py}.log"; }
"$PYTHON" "$ROOT/code/check_models.py" > model-checks.json
"$PYTHON" "$ROOT/code/check_unsymmetric.py" > unsymmetric-checks.txt
"$PYTHON" "$ROOT/code/check_symmetric.py" > symmetric-checks.txt
run check_first_correction.py
run check_wick.py
run check_inverse.py
run check_radial_and_wick.py
run check_saddle_k3.py
run check_saddle_k3_order2.py
run check_second_pairings.py
run check_second_independent.py
run check_numerics.py
for dim in 2 3 symbolic; do
 "$PYTHON" "$ROOT/code/generate_coefficients.py" --k "$dim" --order 2 --output "generator-k${dim}-order2.json"
done
mv generator-ksymbolic-order2.json generator-symbolic-order2.json
"$PYTHON" "$ROOT/code/evaluate_model.py" inverse --k 3 --target 1e100 --order 2 > inverse-example.json
"$PYTHON" "$ROOT/code/evaluate_model.py" forward --k 3 --n 80 --order 2 > forward-example.json
"$PYTHON" - "$ROOT" <<'PY'
import json, pathlib, sys
root=pathlib.Path(sys.argv[1]); expected=root/'data'; count=0
for path in sorted(expected.iterdir()):
    if path.suffix not in {'.json','.txt'}:
        continue
    actual=pathlib.Path(path.name)
    if not actual.exists():
        raise AssertionError('missing replay output '+path.name)
    if path.suffix=='.json':
        assert json.loads(actual.read_text())==json.loads(path.read_text()), path.name
    else:
        assert actual.read_text()==path.read_text(), path.name
    count+=1
summary={'status':'All exact replay comparisons passed','compared_data_files':count,
         'fixed_dimension_generator':'k=2, k=3 and symbolic k through d2',
         'inverse_formal_residual':'zero through degree four'}
pathlib.Path('replay-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
PY
cd "$ROOT"
cp ordered_rook_paths.pdf .replay/original.pdf
bash build.sh
cmp .replay/original.pdf ordered_rook_paths.pdf
"$PYTHON" code/verify_manifest.py
printf 'PASS: exact checks, regenerated data, and byte-identical PDF rebuild\n'
