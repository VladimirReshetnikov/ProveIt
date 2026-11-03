#!/usr/bin/env python3
"""Independent table/recipe reconstruction and generator controls, not Lean."""
import ast
import gzip
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

if sys.flags.optimize or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('isolated non-optimized Python required')
D = Path(__file__).resolve().parents[2]
R = D/'research'
P = R/'direct-bfs-lean-kernel-prototype'
lean = P/'DirectBFSSymbolicKernel.lean'
source = R/'indexed-tile-enumeration/TILES.json'
payload = R/'indexed-tile-enumeration/coefficients/K.bin.gz'
candidate = R/'ten-positive-unshift-t-finite/coefficients/K.bin.gz'
slots_source = R/'ordinary12-ipra-bridge/compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean'
mass_source = R/'ordinary12-ipra-bridge/compact44-coefficient-mass-prototype/CompactCoefficientMass.lean'
generator, author_check = P/'generate.py', P/'check-bytes.py'
inputs = [lean,source,payload,candidate,slots_source,mass_source,generator,author_check]
h = lambda data: hashlib.sha256(data).hexdigest()
before = {str(x):h(x.read_bytes()) for x in inputs}
def need(ok,msg):
    if not ok: raise RuntimeError(msg)

need(before[str(source)] == 'f06d1b9858281f1adcbc431d3c0df9b07df1a231793629650b2d3c09eac56549','table pin')
need(before[str(lean)] == '8a1cd03117bae77e3ed13a853f5bff658ba3acf6ef7dd77bff520cd5cc7f1129','Lean table pin')
txt=lean.read_text()
prefix='def rows : List (Nat × Nat × Nat × Nat) := [\n'
need(txt.count(prefix)==1 and txt.count('\n  ]\n')==1,'table markers')
rows=ast.literal_eval('['+txt.split(prefix)[1].split('\n  ]\n')[0]+']')
table=json.loads(source.read_text())
need(len(rows)==943 and rows==[tuple(row) for row in table], 'row transcription/order')
need(all(len(row)==4 and all(type(x) is int for x in row) and
         0<=row[0]<256 and 0<=row[1]<512 and 0<=row[2]<256 and 0<=row[3]<512 for row in rows),'widths')
slot_text=slots_source.read_text()
m=re.search(r'^def slots : List ℕ := \[([0-9,]+)\]$',slot_text,re.M)
need(m is not None,'slot source')
slots=ast.literal_eval('['+m.group(1)+']')
need(len(slots)==len(set(slots))==41 and all(0<=x<4393 for x in slots),'positions')
mass_text=mass_source.read_text()
need('t.1 + 2^8*t.2.1 + 2^17*t.2.2.1 + 2^25*t.2.2.2 + 127*2^34' in mass_text and
     '1 + 2^10 * (2^41 - value t)' in mass_text,'coefficient definitions')
def value(row):
    w,n,e,s=row
    return w+2**8*n+2**17*e+2**25*s+127*2**34
values=list(map(value,rows))
need(all(0<x<2**41 for x in values),'value bounds')
selectors=[1+2**10*(2**41-x) for x in values]
selector_mass=sum(selectors)
copy_mass=sum(2**(10+j) for j in range(41))
stencil_mass=2*(selector_mass+copy_mass)+6
need((selector_mass,copy_mass,stencil_mass)==(12777109108488111,2251799813684224,30057817844344676),'coefficient mass')
need(3*stencil_mass+1<2**66 and 3*stencil_mass+1+2**66<2**67 and
     3*stencil_mass+(2**67-1)+1<=2*(2**67-1),'mass bounds')

# Unlike the author's direct power sum, accumulate reflected coefficients by
# exponent first and use Horner evaluation in radix 2^67 (including collisions).
coeff={}
def add(e,c): coeff[e]=coeff.get(e,0)+c
for e in (30,62,1100,2201): add(e,1)
for i,c in enumerate(selectors):
    for target in (4393,5495): add(target-i,c)
for j,pos in enumerate(slots):
    for target in (4393,5495): add(target-pos,2**(10+j))
add(8807+42,1)
K=0
for e in range(max(coeff),-1,-1): K=(K<<67)+coeff.get(e,0)
raw=K.to_bytes((K.bit_length()+7)//8,'little')
need(raw==gzip.decompress(payload.read_bytes())==gzip.decompress(candidate.read_bytes()),'kernel payload comparison')
need(h(raw)=='0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f' and len(raw)==74111 and K.bit_length()==592884,'kernel metadata')

run=lambda script,*args: subprocess.run([sys.executable,'-I','-S','-B',str(script),*args],capture_output=True,text=True,timeout=120)
generation=run(generator,'--check')
need(generation.returncode==0 and generation.stdout=='exact transcription check passed\n' and generation.stderr=='','generator check')
author=run(author_check)
author_result=json.loads(author.stdout)
need(author.returncode==0 and not author.stderr and author_result['status']=='PASS_EXTERNAL_RECIPE_BYTES' and
     author_result['raw_sha256']==h(raw),'author byte comparison')
need(author.stdout==(P/'observations/bytecheck-attempt01/stdout').read_text(),'archived byte output')

# Run generator guards in an isolated matching source layout.
with tempfile.TemporaryDirectory(prefix='direct-bfs-gen-review-') as tmp:
    research=Path(tmp)/'research'
    g=research/'direct-bfs-lean-kernel-prototype'
    g.mkdir(parents=True)
    t=research/'indexed-tile-enumeration/TILES.json'
    t.parent.mkdir(parents=True)
    shutil.copyfile(generator,g/'generate.py')
    shutil.copyfile(lean,g/lean.name)
    shutil.copyfile(source,t)
    valid=run(g/'generate.py','--check')
    overwrite=run(g/'generate.py')
    need(valid.returncode==0 and overwrite.returncode!=0 and 'refusing to overwrite' in overwrite.stderr,'generator overwrite guard')
    old=t.read_bytes();t.write_bytes(old+b'\n')
    bad_table=run(g/'generate.py','--check')
    need(bad_table.returncode!=0 and 'unexpected input hash' in bad_table.stderr,'table tamper')
    t.write_bytes(old)
    with (g/lean.name).open('a') as f: f.write('\n')
    bad_lean=run(g/'generate.py','--check')
    need(bad_lean.returncode!=0 and 'table transcription mismatch' in bad_lean.stderr,'Lean tamper')
    controls={'overwrite':overwrite.returncode,'table_tamper':bad_table.returncode,'lean_tamper':bad_lean.returncode}
need(before=={str(x):h(x.read_bytes()) for x in inputs},'inputs changed during check')
print(json.dumps({'status':'PASS_DIRECT_BFS_EXTERNAL_RECONSTRUCTION','input_sha256':before,
                  'rows':len(rows),'positions':len(slots),'payload_bytes':len(raw),'payload_bits':K.bit_length(),
                  'raw_sha256':h(raw),'selector_mass':selector_mass,'copy_mass':copy_mass,'stencil_mass':stencil_mass,
                  'generator_controls':controls,'scope':'external source/table and recipe comparison; no Lean/file equality or machine theorem'},
                 indent=2,sort_keys=True))
