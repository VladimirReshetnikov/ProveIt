"""Compare the recorded 87-parent source snapshot to current workspace files."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[4]; here=Path(__file__).resolve().parent
p=here/'guards.json'; data=json.loads(p.read_text()); rows=[]
for n,rec in data['guards'].items():
 f=R/rec['path'];actual=hashlib.sha256(f.read_bytes()).hexdigest() if f.is_file() else None
 if actual!=rec['sha256']:rows.append({'module':n,'path':rec['path'],'expected_sha256':rec['sha256'],'actual_sha256':actual})
print(json.dumps({'guard_manifest_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'guard_count':len(data['guards']),'drift_count':len(rows),'drift':rows},indent=2))
