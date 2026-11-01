#!/usr/bin/env python3
"""Run precisely the frozen replay's preflight without allocating a build."""
from pathlib import Path
import hashlib,json,sys
D=Path(__file__).resolve().parent;V=D.parent;P=V/'ipra-current-repaired-post120-replay';R=P/'replay.py';M=P/'manifest.json';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();rh=H(R);mh=H(M);sh=H(__file__);raw=R.read_text();marker="frozen()\nw = Path(tempfile.mkdtemp(prefix='ipra-post120-replay-'))";assert raw.count(marker)==1;prefix=raw.split(marker)[0]+'frozen()\n';sys.argv=[str(R),mh];scope={'__name__':'__preflight__','__file__':str(R.resolve())};exec(compile(prefix,str(R),'exec'),scope);assert H(R)==rh and H(M)==mh and H(__file__)==sh
out={'status':'PASS_FROZEN_REPLAY_PREFLIGHT','manifest_sha256':mh,'replay_sha256':rh,'audit_sha256':sh,'executed_prefix_sha256':hashlib.sha256(prefix.encode()).hexdigest(),'scope':'Exactly the replay preflight, excluding workspace-drift qualification and excluding any Lean build.'};p=D/'receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],H(p))
