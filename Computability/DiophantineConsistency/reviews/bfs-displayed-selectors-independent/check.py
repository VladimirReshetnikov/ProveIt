#!/usr/bin/env python3
"""Compare PDF selector transcription, pinned BFS table and saved Lean receipt; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re,subprocess
D=Path(__file__).resolve().parents[2];R=D/'research';P=R/'ten-positive-80-bfs-selectors-lean';S=P/'BFSDisplayedSelectors.lean';PDF=R/'ten-positive-80-bfs-decimal-display/equation.pdf';TABLE=R/'direct-bfs-lean-kernel-prototype/DirectBFSSymbolicKernel.lean';DATA=R/'indexed-tile-enumeration/TILES.json';O=P/'observations/attempt01';t=json.loads((O/'terminal.json').read_text())
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert t['status']=='PASS' and t['exit']==0 and t['reason'] is None and sha(S)==t['source_sha256']=='d507a86572b5043964d1ec5a5f60e39c9107e5ecc3d72600abc124de5a984dcb';assert sha(P/'run.py')==t['runner_sha256'] and sha(t['output'])==t['output_sha256']=='92f60899906162de5e0ff953b4f9f0041f7471d17ee65e31a90db33b6363c65f'
for path,z in t['pins'].items():assert sha(path)==z['sha256'] and str(Path(path).resolve())==z['resolved'],path
assert sha(PDF)=='412ebf276d1e3d9b2802d333e020a4b7579f2368660bdede31be665564e40fe7';assert sha(O/'stdout')==t['stdout_sha256'] and sha(O/'stderr')==t['stderr_sha256'] and (O/'stdout').read_text()=="'BFSDisplayedSelectors.values_eq_rows_map' depends on axioms: [propext]\n" and not (O/'stderr').read_text()
source=S.read_text();assert re.findall(r'^import\s+(\S+)',source,re.M)==['DirectBFSSymbolicKernel'] and not re.search(r'\b(?:sorry|admit)\b',source)
assert re.search(r'theorem values_eq_rows_map\s*:\s*values\s*=\s*DirectBFSSymbolicKernel.rows.map CompactCoefficientMass.selector\s*:=\s*by\s*decide',source)
lean=[int(x) for x in re.findall(r'\d+',source.split('def values : List ℕ := [',1)[1].split(']',1)[0])]
text=subprocess.run(['pdftotext','-layout',str(PDF),'-'],capture_output=True,text=True,check=True);assert not text.stderr
pdf=[int(x) for x in re.findall(r'(?<!\d)\d{14}(?!\d)',text.stdout.split('Decimal selector list.',1)[1])]
table=TABLE.read_text().split('def rows : List (Nat × Nat × Nat × Nat) := [',1)[1].split(']',1)[0];rows=[tuple(map(int,x)) for x in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)',table)];assert rows==[tuple(x) for x in json.loads(DATA.read_text())]
expected=[1+2**10*(2**41-(w+256*n+2**17*p+2**25*s+127*2**34)) for w,n,p,s in rows];assert len(lean)==len(pdf)==len(rows)==943 and lean==pdf==expected
provider=Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib/DirectBFSSymbolicKernel.olean');assert sha(provider)==t['pins'][str(provider)]['sha256']=='69f4a2f9d32229b6846ec7f0b84fe4b4d69d5eba8de1ff5c9ddb063e1d855c3f'
print('PASS 943 PDF selectors = Lean list literals = independently recomputed BFS source/JSON selectors; recorded Lean finite-list equality, direct provider',sha(provider))
print('External PDF/text transcription and source-object/package/dynamic ancestry remain separate; no independent Lean replay.')
