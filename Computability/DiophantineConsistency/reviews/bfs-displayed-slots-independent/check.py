#!/usr/bin/env python3
"""Inspect explicit slot and symbolic BFS recipe Lean receipt; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re,subprocess
D=Path(__file__).resolve().parents[2];R=D/'research';P=R/'ten-positive-80-bfs-slots-lean';S=P/'BFSDisplayedSlots.lean';O=P/'observations/attempt01';PDF=R/'ten-positive-80-bfs-decimal-display/equation.pdf';TEX=PDF.with_suffix('.tex');K=R/'ordinary12-ipra-bridge/compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean';t=json.loads((O/'terminal.json').read_text())
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'terminal.json')=='11055517cf6a2528b99dcacd09229ce1876fb3f79eff21445dff2fea07566c3f' and t['status']=='PASS' and t['exit']==0 and t['reason'] is None
assert sha(S)==t['source_sha256']=='c673d538a69de08334c25b5109fc86ee8a70772d87db347415b0c015009f80d6' and sha(P/'run.py')==t['runner_sha256'] and sha(t['output'])==t['output_sha256']=='232a18c1544fa215d694391c3fa9fca75abb3eb1ae202f51c624d5a22147ee66'
for path,z in t['pins'].items():assert sha(path)==z['sha256'] and str(Path(path).resolve())==z['resolved'],path
assert sha(PDF)=='412ebf276d1e3d9b2802d333e020a4b7579f2368660bdede31be665564e40fe7' and sha(TEX)=='be7181e835a2b530da007b7b856ea9a799db2f2ad05aef8036a3a95ed21cd849';assert sha(O/'stdout')==t['stdout_sha256'] and sha(O/'stderr')==t['stderr_sha256'] and (O/'stdout').read_text()=="'BFSDisplayedSlots.kernel_eq_displayed' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (O/'stderr').read_text()
s=S.read_text();assert re.findall(r'^import\s+(\S+)',s,re.M)==['BFSDisplayedKernelV4'] and not re.search(r'\b(?:sorry|admit)\b',s)
assert re.search(r'theorem values_eq_slots\s*:\s*values\s*=\s*CompactSymbolicKernel.slots\s*:=\s*by\s*rfl',s) and re.search(r'theorem kernel_eq_displayed \(r : ℕ\) :\s*DirectBFSSymbolicKernel.paramKernel r = displayedKernel r',s)
assert 'BFSDisplayedKernel.displayedSelector i' in s and '(4393-displayedPosition i)' in s and '(5495-displayedPosition i)' in s and 'r^8849' in s
slots=[int(x) for x in re.findall(r'\d+',s.split('def values : List ℕ := [',1)[1].split(']',1)[0])];source=[int(x.strip()) for x in K.read_text().split('def slots : List ℕ := [',1)[1].split(']',1)[0].split(',')]
text=subprocess.run(['pdftotext','-layout',str(PDF),'-'],capture_output=True,text=True,check=True);assert not text.stderr
pages=text.stdout.replace('µ','μ').split('\f');printed=[int(x) for x in re.findall(r'\d+',pages[1].split('λ = (',1)[1].split(').',1)[0])];assert len(slots)==41 and slots==source==printed
prov=Path('/tmp/bfs-printed-kernel-orsko0l9/BFSDisplayedKernelV4.olean');assert sha(prov)==t['pins'][str(prov)]['sha256']=='bd6b509d78529c1c9879774a11989d605849c282ba4d408ef1ecfe1ed36bc072'
print('PASS ordered 41 PDF slots = Lean literals = CompactSymbolicKernel source slots; Lean ∀r recipe uses selector and slot lists')
print('PDF/text transcription and source-object/package/dynamic ancestry remain external; no Lean replay.')
