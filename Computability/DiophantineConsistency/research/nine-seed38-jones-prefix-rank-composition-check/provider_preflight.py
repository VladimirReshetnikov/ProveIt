#!/usr/bin/env python3
"""Point checks for both independently reviewed producers; no Lean."""
import hashlib, json, os, subprocess, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent; D=P.parents[1]
sha=lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,check,result in [
 ('nine-seed38-jones-rankcode-link-terminal-frontier-independent','ec8061093e2a42e153d791b29046ee0b5b19ef2eb376ca172ad1dce331a824f3','db68e5eac671cb33932cdc7685094bef79108baaca0684f7710dadfa39019e9e'),
 ('nine-seed38-jones-prefix-b-power-terminal-frontier-independent','871406c1c31644a002df6210692122b732b8cdd833c518a9de72b7e6c6785871','f9deaf23fc0870a7d0acd7d3a56a129d626e0254acd28dba201aaec602a93b9a')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=check or sha(q/'result.json')!=result: raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-prefix-rank-composition-draft/Norm38MacroRankComposition.lean'
if sha(draft)!='7456d37335417d1aec5cf8ed97d1d1cb9eaa117d27f5a8a04fb945dbab3771ca':raise RuntimeError('source')
a=D/'research/nine-seed38-jones-rankcode-link-check/attempt01/state.json';b=D/'research/nine-seed38-jones-prefix-b-power-check/attempt01/state.json'
if sha(a)!='6a91660e068615b3b53c5c90f9badd8124c4ef75bb9163e79e2dd0907460314a' or sha(b)!='c524139780b3cb4f1e3b66c03f8829bd1cbbd204bb6ef01ffb86f4fa962b067a':raise RuntimeError('states')
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
 ('Norm38MacroRankCodeLink','/tmp/nine-seed38-jones-rankcode-link-check-20261106/lib/DiophantineConsistency/Norm38MacroRankCodeLink.olean','5a200be6ed07ad99ee680339c8a6383f4140f586fb1dcb311ad4e7eea1557259'),
 ('Norm38MacroPrefixBPower','/tmp/nine-seed38-jones-prefix-b-power-check-20261106/lib/DiophantineConsistency/Norm38MacroPrefixBPower.olean','e66a9ddbe1f06f6d2e593939a077494517f7351731ed41106eb23645fd26b27b')]:
 p=Path(p)
 if not p.is_file() or sha(p)!=h:raise RuntimeError(('producer',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'shared_overlay_paths':len(by),'scope':'Two audited producers and overlay comparison; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
