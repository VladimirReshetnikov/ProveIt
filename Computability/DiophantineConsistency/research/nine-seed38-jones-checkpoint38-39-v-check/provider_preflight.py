#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-checkpoint37-41-a1-terminal-frontier-independent', '4401d52c930412ee28182a680d6f97d05f0aa8de7f7fb6a5ecfe67aa8d768f45', '22f958b666fa75d8533330c52d525c9fb15bdf50e19332b6f8e1d75e7eba55dc'), ('nine-seed38-jones-dependent07-staged-terminal-frontier-independent', '3131f0ac15437151abbf12ec026b35630df58542d0b1d4f4f63dc3dc14f169a8', '6dea09a5229acfc79d3dc1afa8380370ae173632b4cbde02acec4e12e452b3f9')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-checkpoint38-39-v-draft'
for n,h in [('Norm38MacroV0Value', 'fa3a273626982de1411960918b2a4041684efd3e887fe7f6343e263d1c523154'), ('Norm38MacroV1Value', '970afa5a77f7c2e196c26da778a8645fb2946a019c68eae74c327625cb81bd1a')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint37-41-a1-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroA1Path', '/tmp/nine-seed38-jones-checkpoint37-41-a1-check-20261106/lib/DiophantineConsistency', '25cbbb07e0f5e0cf6190b544c5214d8f9ec6033f4357bd0565e74fd2729fef63'), ('Norm38MacroDependentV', '/tmp/nine-seed38-jones-dependent07-staged-check-20261106/lib/DiophantineConsistency', '93889388c58ac41b046d81d22bbdfd748ac726704bef2efe01ca6a132048d147')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Two audited A1 and V-node producers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
