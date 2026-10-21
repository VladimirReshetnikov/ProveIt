#!/usr/bin/env python3
from pathlib import Path
import sys,json,hashlib,time
HERE=Path(__file__).resolve().parent;sys.path.insert(0,str(HERE.parent))
import verify_candidate_runtime as v
import symbolic_premise as p
mapping={int(k):int(x)for k,x in json.loads((v.REF/'inputs/legacy_mapping.json').read_text()).items()}
receipt=p.install(v.s,mapping[34]);started=time.monotonic();code=v.main()
receipt['overapproximated_prefix_languages']=sorted(receipt['overapproximated_prefix_languages'])
receipt.update(status='ALL_QUANTIFIED_INTERFACES_AND_SCANNER_PREMISES_PROVED'if code==0 else'NOT_PROVED',seconds=time.monotonic()-started,table_sha256=v.digest(Path(sys.argv[1])),sites_sha256=v.digest(Path(sys.argv[2])),prefix_checker_sha256=v.digest(HERE/'symbolic_premise.py'),driver_sha256=v.digest(Path(__file__)))
(Path(sys.argv[3])/'scanner_premise.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2),flush=True)
raise SystemExit(code)
