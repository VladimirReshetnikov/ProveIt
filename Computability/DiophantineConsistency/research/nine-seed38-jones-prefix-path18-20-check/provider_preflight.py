#!/usr/bin/env python3
"""Point checks for both independently reviewed producers; no Lean."""
import hashlib, json, os, subprocess, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent; D=P.parents[1]
sha=lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,check,result in [
 ('nine-seed38-jones-dependent08-staged-terminal-frontier-independent','c9093ca2c52b810bf0f2d878bb513aa54502b0b2fa13146b11e4e35fbf62d26e','f59e7238d645a2eebab7b13fd342d5a1045ea3b53331e7e40620b2223407678c'),
 ('nine-seed38-jones-prefix-embedding-terminal-frontier-independent','4d0bb7d3decdb896a4e0c366d1e2bf88209b2b831ab5d50c119819e244a031cf','d9968c1d2a150b71f9998e7355df4c422bc494f72e0e747b50ef30e01d4f89af')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=check or sha(q/'result.json')!=result: raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-prefix-path18-20-draft/Norm38MacroPath18to20.lean'
if sha(draft)!='0d5129bfa5fc3fedc920db2a484fc6ab83f4f364350f936490640d4e95ea7196':raise RuntimeError('source')
a=D/'research/nine-seed38-jones-dependent08-staged-check/attempt01/state.json';b=D/'research/nine-seed38-jones-prefix-embedding-check/attempt01/state.json'
if sha(a)!='3cbc8a506a81c3f7ef2a25e845049cb715623a36052ac55f7da0d952dae4cacf' or sha(b)!='9e8939bb926fd5d1e88721240579b4fd5c4eccadacbbb2c4c23f9c4dfeb44a5d':raise RuntimeError('states')
x=json.loads(a.read_text());y=json.loads(b.read_text())
# Strip the output-root prefix at the lib directory, retaining module-relative keys.
def librels(s):
 result={}
 for k,v in s['overlay_links'].items():
  if '/lib/' not in k:raise RuntimeError(('overlay shape',k))
  rel=k.split('/lib/',1)[1]
  if rel in result:raise RuntimeError(('duplicate overlay',rel))
  result[rel]=v
 return result
ax,by=librels(x),librels(y)
if any(k not in ax or ax[k]!=v for k,v in by.items()):raise RuntimeError('overlay disagreement')
selected={}
for n,p,h in [
 ('Norm38MacroDependentOutput','/tmp/nine-seed38-jones-dependent08-staged-check-20261106/lib/DiophantineConsistency/Norm38MacroDependentOutput.olean','39ae6b92258383e0505623a46c01a5ca71952561593a71090c0685508a7f8f58'),
 ('Norm38MacroPrefixEmbedding','/tmp/nine-seed38-jones-prefix-embedding-check-20261106/lib/DiophantineConsistency/Norm38MacroPrefixEmbedding.olean','a7f4b4f604505643e057e48a3f30ee5aaba9780348ee3edbb4ce3a58b58218be')]:
 p=Path(p)
 if not p.is_file() or sha(p)!=h:raise RuntimeError(('producer',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'shared_overlay_paths':len(by),'scope':'Two audited producers and overlay comparison; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
