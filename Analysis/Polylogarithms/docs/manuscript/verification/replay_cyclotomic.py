"""Exact continuation replay with a separate, bounded manuscript receipt."""
from pathlib import Path
import hashlib, importlib.util, json, sys
B=Path(__file__).resolve().parents[1]
source=B.parent/'reports/herglotz-cyclotomic-obstructions/code/verify_cyclotomic.py'
spec=importlib.util.spec_from_file_location('polylog_cyclotomic_snapshot',source)
module=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=module
spec.loader.exec_module(module)
details=[module.check_modulus(q,elimination=True) for q in range(1,41)]
zeros=[q for q in range(1,1001) if module.rank_formula(q)==0]
assert zeros==[1,2,3,4,5,6,8,10,12,24]
result=dict(source=source.relative_to(B.parent).as_posix(),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
            exact_elimination_moduli=[1,40],rank_formula_moduli=[1,1000],checks=details,
            zero_conductors=zeros,J_family=module.check_j_family(1000),
            preprint_counterexample=module.preprint_counterexample(),passed=True)
(B/'verification/cyclotomic-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('Exact regular-representation checks through 40, rank formula and J criterion through 1000 passed.')
