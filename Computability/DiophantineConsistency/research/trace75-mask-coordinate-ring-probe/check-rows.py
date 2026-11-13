#!/usr/bin/env python3
"""Read-only row-to-candidate check for the accepted trace74 Lean source."""
from hashlib import sha256
from pathlib import Path
import json,re
H=Path(__file__).resolve().parent
C=H.parent/'trace74-mask-coordinate-probe/candidate.json'
S=H/'Trace74Mask.lean'; T=H/'observations/ring-attempt02/terminal.json'; P=H/'observations/provider-attempt01/terminal.json'
def sha(p):return sha256(p.read_bytes()).hexdigest()
assert sha(C)=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'
assert sha(S)=='83ad7a62d50b10104099d8769c201c5514ed3afdabcf30ce1df8f4bb7774b7f0'
assert sha(T)=='4be85ee6a9e08695c3f67e1d1154108cdb601308ac4c1da46b6f4a24e9559fc9'
assert sha(P)=='6eb7be2e3193f46f2a0d889083f9d1917a470cab31e28abc866f47d65324d700'
t=json.loads(T.read_text());p=json.loads(P.read_text());assert t['exit']==p['exit']==0 and t['reason'] is p['reason'] is None
assert t['object_sha256']=='181b53fe5c5a52127a56ab25af95d0b7fda3d9842098850a70c8afc70659861e'
assert p['object_sha256']=='1ae82441c7023e9675c5cc532d4026da6a3ee77e906996d67c315e4f693b079c'
assert sha(H/'observations/ring-attempt02/source.txt')==sha(S)
text=S.read_text().split('def value74 ',1)[1].split('\ndef core ',1)[0]
inputs=re.findall(r'^  let (\w+) : R := ([vp]) (\d+)$',text,re.M)
assert inputs==[(n,'v',str(i)) for i,n in enumerate(['J','F','C','i','T','w','s','n','eta','zeta'])]+[(n,'p',str(i)) for i,n in enumerate(['beta','K0','MC','MF'])]
rows=[list(x) for x in re.findall(r'^  let (\w+) := (\w+) ([+*\-]) (\w+)$',text,re.M)]
# Lean identifier cannot begin with a digit; numbers are JSON integers.
def normalize(x):
 if x=='fourAm1':return '4Am1'
 return int(x) if x.isdigit() else x
rows=[[normalize(n),op,normalize(a),normalize(b)] for n,a,op,b in rows]
d=json.loads(C.read_text());assert rows==d['source'];assert len(rows)==74
assert text.rstrip().endswith('N') and d['output']=='N'
print('PASS: exact 74 ordered rows, 10 witness slots, 4 port slots and output; accepted source and provider receipts pinned')
print('Scope: external row comparison only; no Lean JSON parser or positive-domain/iPRA equivalence.')
