#!/usr/bin/env python3
"""Read-only exact-byte and fake-child review; no Lean compiler is launched."""
import hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge/compact44-high-residue-prototype';HERE=Path(__file__).resolve().parent
DRIVER=PKG/'replay.py';D='20a5eadfcc0f098111ebcaa323213eb541ec8a87ed087d237d26f62605ccb764'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
def main():
 prefix=PKG.relative_to(ROOT).as_posix()+'/'
 names=subprocess.run(['git','ls-tree','-r','--name-only','b8fab3df3e','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines();need(len(names)==4,'inventory')
 for n in names:
  b=subprocess.run(['git','show','b8fab3df3e:'+n],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(b).hexdigest()==sha(ROOT/n),'packet '+n)
 need(sha(DRIVER)==D,'driver');sp=importlib.util.spec_from_file_location('review',DRIVER);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
 for p,h in m.PINS.items():need(sha(p)==h,'pin '+str(p))
 need(len(m.PINS)==7 and m.EXPECTED=="'CompactHighResidue.natural_mod_eight' depends on axioms: [propext]\n'CompactHighResidue.model_mod_eight' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'exact reports')
 source=m.SOURCE.read_text();need('highDigits = 4 :: highDigits.tail' in source and 'cast_mod (V:=V)' in source and source.count('#print axioms ')==2,'source claims')
 m.PINS={m.SOURCE:'0'*64}
 try:m.verify();raise ValueError('altered pin accepted')
 except ValueError as e:need('input drift' in str(e),'bad pin guard')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(HERE/'mock_loop.py')],capture_output=True,text=True,timeout=120);need(q.returncode==0 and not q.stderr and len(q.stdout.splitlines())==10,'fake loop')
 qopt=subprocess.run([sys.executable,'-I','-S','-O',str(DRIVER),'--output','/tmp/ipra-compact-high-residue-pair-review-optimized'],capture_output=True,text=True,timeout=30);need(qopt.returncode!=0 and 'without optimization' in qopt.stderr,'optimized guard')
 qisolation=subprocess.run([sys.executable,'-S','-B',str(DRIVER),'--output','/tmp/ipra-compact-high-residue-pair-review-not-isolated'],capture_output=True,text=True,timeout=30);need(qisolation.returncode!=0 and 'without optimization' in qisolation.stderr,'isolation guard')
 qsite=subprocess.run([sys.executable,'-I','-B',str(DRIVER),'--output','/tmp/ipra-compact-high-residue-pair-review-with-site'],capture_output=True,text=True,timeout=30);need(qsite.returncode!=0 and 'without optimization' in qsite.stderr,'no-site guard')
 qout=subprocess.run([sys.executable,'-I','-S','-B',str(DRIVER),'--output','/tmp'],capture_output=True,text=True,timeout=30);need(qout.returncode!=0 and 'need fresh dedicated' in qout.stderr,'output guard')
 print(json.dumps({'status':'PASS_COMPACT_HIGH_RESIDUE_PRELAUNCH_REVIEW','source_commit':'b8fab3df3e','driver_sha256':D,'fixed_pins':7,'mock_exit':q.returncode,'mock_stdout':q.stdout,'optimized_exit':qopt.returncode,'nonisolated_exit':qisolation.returncode,'site_enabled_exit':qsite.returncode,'invalid_output_exit':qout.returncode,'scope':'No Lean launched; symbolic finite-list natural and IΣ₁ model residue only, no retained high-port equality or internal PRA endpoint; inherited provider, trusted initial loader, stable HEAD, sampled resource and unmonitored dependency limits.'},indent=2))
if __name__=='__main__':main()
