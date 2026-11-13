#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-checkpoint34-41-h-terminal-frontier-independent', 'd0fff952362b8629282affc54d3d5ccf20e013bd4d2d22cffaf779b83751cbc3', '0dffca221521243135168c4b8fd86247e644fd5f51d47c628aac4bc1f8647e79'), ('nine-seed38-jones-checkpoint33-41-gprime-terminal-frontier-independent', 'c8f34bdd959f82ed77df8d665efb843f6de2dfdec274620cd770e57893c6c2bc', '8a5566c1cdb9e0f00ad5490759a17e2df39bdeea5d0a27deac2a453a457a2d5a'), ('nine-seed38-jones-dependent07-staged-terminal-frontier-independent', '3131f0ac15437151abbf12ec026b35630df58542d0b1d4f4f63dc3dc14f169a8', '6dea09a5229acfc79d3dc1afa8380370ae173632b4cbde02acec4e12e452b3f9')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint35-41-i-draft'
for n,h in [('Norm38MacroIValue', 'b8b667a072ac2dc69c5318554b887592f08ba1a2b161760ece81204832b43c99'), ('Norm38MacroIPath', 'c817dc8334bb95f2eabd7d0660d5522fcbdfc407b7df1a179b6fc59557d78179')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint34-41-h-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroHPath', '/tmp/nine-seed38-jones-checkpoint34-41-h-check-20261106/lib/DiophantineConsistency', 'd6f64fff7c7175db02b85101b9f4f112290cea47a6a80bb6ae1cee9344a20462'), ('Norm38MacroDependentI', '/tmp/nine-seed38-jones-dependent07-staged-check-20261106/lib/DiophantineConsistency', 'c12051c12de47d4971c060cd6f4e7c1da0f0962a585f5c093861274606442d72')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Three audited H, Gprime and I-node producers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
