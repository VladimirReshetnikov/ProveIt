#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent;out=R/'sections';out.mkdir(exist_ok=True);rows=[]
for name in ['quartic','encoding','nine','signed108trim','signed13','positive','alternatives']:
 p=R/name/'section.tex';s=p.read_text();q=out/(name+'.tex');q.write_text(s)
 rows.append({'source':str(p.relative_to(R)),'layout_copy':str(q.relative_to(R)),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'layout_sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'changes':[]})
(R/'SECTION_LAYOUT_MAP.json').write_text(json.dumps(rows,indent=2)+'\n');print('Built seven TeX section copies.')
