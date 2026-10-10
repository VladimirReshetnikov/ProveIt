"""Replay the spectral continuation into an isolated output directory."""
from pathlib import Path
import hashlib, importlib.util, json, sys
B=Path(__file__).resolve().parents[1]
source=B.parent/'reports/rational-grid-distribution-ranks/code/10-exact-structure-parameter_asymptotics.py'
spec=importlib.util.spec_from_file_location('polylog_spectral_snapshot',source)
module=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=module
spec.loader.exec_module(module)
destination=B/'verification/spectral-replay'
destination.mkdir(parents=True,exist_ok=True)
module.ROOT=destination
sys.argv=[str(source),'--quick','--no-figure']
module.main()
(destination/'source.json').write_text(json.dumps(dict(path=source.relative_to(B.parent).as_posix(),
 source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),configuration=['--quick','--no-figure']),indent=2)+'\n',encoding='utf-8')
