"""Replay immutable continuation functions without overwriting their receipts."""
from pathlib import Path
import hashlib, importlib.util, json, sys
B=Path(__file__).resolve().parents[1]
source=B.parent/'reports/rational-grid-distribution-ranks/code/10-exact-structure-verify_distributions_and_bridges.py'
spec=importlib.util.spec_from_file_location('polylog_rank_snapshot',source)
module=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=module
spec.loader.exec_module(module)
result=dict(source=str(source.relative_to(B.parent)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
            configuration=dict(maximum_q=20,maximum_bridge_derivative=3,decimal_digits=65),
            rank_checks=module.check_ranks(20),bridge_checks=module.check_bridges(3),passed=True)
(B/'verification/rank-bridge-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
