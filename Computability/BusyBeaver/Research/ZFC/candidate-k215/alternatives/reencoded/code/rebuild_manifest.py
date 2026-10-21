from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent.parent
files={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest()for p in sorted(R.rglob('*'))if p.is_file()and '__pycache__'not in p.parts and p.name!='manifest.json'}
(R/'manifest.json').write_text(json.dumps(dict(schema='SHA256_EXACT_FILES_V1',files=files),indent=2)+'\n')
