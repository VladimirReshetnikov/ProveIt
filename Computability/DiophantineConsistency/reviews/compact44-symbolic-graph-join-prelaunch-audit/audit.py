#!/usr/bin/env python3
"""Independent no-Lean exact-byte review of the corrected symbolic join replay."""
import hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge/compact44-symbolic-graph-join-prototype';HERE=Path(__file__).resolve().parent;D='71c0e0da4a04e62152a37ac68fd940487d14df2f0ed47cacfdbc35506e7934ad'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 for n in ('replay.py','axiom_controls.py','dependency_controls.py','CompactSymbolicGraphDigits.lean'):
  p=PKG/n;name=p.relative_to(ROOT).as_posix();b=subprocess.run(['git','show','0d2b7a06c4:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(b).hexdigest()==H(p),'committed bytes '+n)
 driver=PKG/'replay.py';need(H(driver)==D,'driver');sp=importlib.util.spec_from_file_location('join_review',driver);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
 for p,h in m.PINS.items():need(H(p)==h,'input pin '+str(p))
 scan,graph,low=m.verify();need(scan['status']=='PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD' and len(scan['modules'])==7 and len(scan['inherited_objects'])==127 and graph['status']=='PASS_INDEPENDENT_FREEJ_CONCRETE_DIGITS_CLIENT_AUDIT' and low['status']=='PASS_INDEPENDENT_COMPACT44_LOW_EVEN_AUDIT','real parent verification')
 for path,lines in ((HERE/'symbolic-join-fake-review.py',14),(HERE/'symbolic-join-guards-review.py',1),(HERE/'symbolic-join-historical-gap.py',1),(PKG/'axiom_controls.py',1),(PKG/'dependency_controls.py',1)):
  q=subprocess.run([sys.executable,'-I','-S','-B',str(path)],capture_output=True,text=True,timeout=120);need(q.returncode==0 and not q.stderr and len(q.stdout.splitlines())==lines,'control '+str(path)+' '+q.stderr)
  if path.name=='symbolic-join-fake-review.py':need('good PASS 14' in q.stdout and 'missing_init PASS 1' in q.stdout,'full loop and Init regression')
  if path.name=='symbolic-join-historical-gap.py':need('HISTORICAL_DRIVER_ACCEPTED_MISSING_INIT 14' in q.stdout,'historical guard gap')
 print(json.dumps({'status':'PASS_SYMBOLIC_GRAPH_JOIN_PRELAUNCH_AUDIT','corrected_driver_commit':'0d2b7a06c4','driver_sha256':D,'source_modules':7,'inherited_objects_per_side':127,'full_parent_verify_exit':0,'fake_compiler_children':14,'negative_fake_modes':13,'historical_missing_init_control':'older 0819ac850a driver accepted fake missing Init','corrected_missing_init_control':'rejected after first fake compiler','scope':'No Lean; graph digit theorem remains conditional on both symbolic port equalities, graph positivity and radix/split/product assumptions. No retained-port calibration, checker, machine or iPRA endpoint. Initial loader/stable HEAD/sole Lean externally trusted; sampled monitor, deps and dynamic/provider limits inherited.'},indent=2))
if __name__=='__main__':main()
