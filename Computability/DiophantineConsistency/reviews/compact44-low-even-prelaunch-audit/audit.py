#!/usr/bin/env python3
"""No-Lean exact source, provider pins and fake-child prelaunch review."""
import hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge/compact44-low-even-prototype';HERE=Path(__file__).resolve().parent
DRIVER=PKG/'replay.py';D='12f9f6d08e5c94f461f0d12770789594f4844f82a0b23c808340e896e2f14890'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
def main():
 for n in ('replay.py','README.md','CompactLowEven.lean','observations/attempt01.lean','observations/attempt01.txt','observations/attempt02.txt'):
  p=PKG/n;name=p.relative_to(ROOT).as_posix();b=subprocess.run(['git','show','30013a45e8:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(b).hexdigest()==H(p),'packet drift '+name)
 need(H(DRIVER)==D,'driver');sp=importlib.util.spec_from_file_location('review',DRIVER);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
 for p,h in m.PINS.items():need(H(p)==h,'input pin '+str(p))
 need(len(m.PINS)==7 and m.EXPECTED=="'CompactLowEven.low_even' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'reports')
 source=m.SOURCE.read_text();need('theorem low_even : (CompactConcreteIncrement.mask : V) % 2 = 0' in source and 'CompactConcreteMask.model_origin' in source,'claim')
 m.PINS={m.SOURCE:'0'*64}
 try:m.verify();raise ValueError('altered pin accepted')
 except ValueError as e:need('input drift' in str(e),'bad pin')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(HERE/'mock_loop.py')],capture_output=True,text=True,timeout=120);need(q.returncode==0 and not q.stderr and len(q.stdout.splitlines())==10,'fake pair')
 modes=[(['-I','-S','-O'],'optimized'),(['-S','-B'],'nonisolated'),(['-I','-B'],'site')];guards={}
 for args,name in modes:
  r=subprocess.run([sys.executable,*args,str(DRIVER),'--output','/tmp/ipra-compact-low-even-pair-review-guard'],capture_output=True,text=True,timeout=30);need(r.returncode!=0 and 'without optimization' in r.stderr,name+' guard');guards[name]=r.returncode
 r=subprocess.run([sys.executable,'-I','-S','-B',str(DRIVER),'--output','/tmp'],capture_output=True,text=True,timeout=30);need(r.returncode!=0 and 'need fresh dedicated' in r.stderr,'output guard');guards['invalid_output']=r.returncode
 print(json.dumps({'status':'PASS_COMPACT_LOW_EVEN_PRELAUNCH_AUDIT','source_commit':'30013a45e8','driver_sha256':D,'fixed_pins':7,'fake_pair_exit':q.returncode,'fake_pair_observations':q.stdout,'guard_exits':guards,'scope':'No Lean; symbolic low-mask evenness in IΣ₁ models. No retained MC or actual graph-port equality, checker, machine or iPRA endpoint. Inherited point-in-time parent/provider limits, trusted initial loader and externally enforced stable HEAD/sole Lean; monitoring sampled and deps unmonitored.'},indent=2))
if __name__=='__main__':main()
