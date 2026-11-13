#!/usr/bin/env python3
"""Independently check the preliminary seven-source graph-join closure, no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';R=BASE/'research/ordinary12-ipra-bridge';PLAN=R/'compact44-symbolic-graph-closure-plan';CLIENT=R/'compact44-symbolic-graph-join-prototype';PREFIX=Path('/tmp/ipra-freej-concrete-digits-client-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
def main():
 for p in (PLAN/'README.md',PLAN/'scan.py',PLAN/'scan.json',CLIENT/'CompactSymbolicGraphDigits.lean'):
  name=p.relative_to(ROOT).as_posix();b=subprocess.run(['git','show','05cfc83473:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(b).hexdigest()==H(p),'pinned bytes '+name)
 p=CLIENT/'README.md';name=p.relative_to(ROOT).as_posix();old=subprocess.run(['git','show','05cfc83473:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;new=subprocess.run(['git','show','b2c594d96d:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(old!=new and hashlib.sha256(new).hexdigest()==H(p),'documented later author-exploration README')
 scan=json.loads((PLAN/'scan.json').read_bytes());need(scan['status']=='PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD' and len(scan['modules'])==7 and len(scan['inherited_objects'])==127,'counts/status')
 for p,h in scan['parent_audits'].items():need(H(p)==h,'receipt '+p)
 libs=[PREFIX/s/'lib' for s in ('author','peer')];inventories=[{p.relative_to(lib):p for p in lib.rglob('*.olean')} for lib in libs];need(inventories[0].keys()==inventories[1].keys() and len(inventories[0])==127,'provider inventories')
 for row in scan['inherited_objects']:
  rel=Path(row['module_path']);a,b=[x[rel] for x in inventories];need(H(a)==H(b)==row['sha256'] and str(a.resolve())==row['author_resolved_path'] and str(b.resolve())==row['peer_resolved_path'],'provider '+str(rel))
 available=set(inventories[0]);modules=[]
 for row in scan['modules']:
  name=row['module'];p=Path(row['source']);need(H(p)==row['source_sha256'],'source '+name)
  imports=[part for line in p.read_text().splitlines() if line.startswith('import ') for part in line[7:].split()];need(imports==row['imports'],'imports '+name)
  for dep in imports:
   rel=Path(*dep.split('.')).with_suffix('.olean');need(rel in available or (not dep.startswith('DiophantineConsistency.') and (PACKAGE/rel).is_file()),'missing dependency or project fallback '+dep)
  rel=Path(*name.split('.')).with_suffix('.olean');need(rel not in available,'collision '+name);available.add(rel);modules.append(name)
 need(len(scan['explicit_choices']['CompactLowPopulation']['all_candidates'])==2,'ambiguous low-population candidates')
 for name,v in scan['explicit_choices'].items():
  need(H(v['selected'])==v['selected_sha256'],'selected '+name)
  for c in v['all_candidates']:need(H(c['path'])==c['sha256'],'candidate '+name)
 q=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,timeout=120);need(q.returncode==0 and not q.stderr and q.stdout==(PLAN/'scan.json').read_bytes(),'fresh scan')
 qopt=subprocess.run([sys.executable,'-I','-S','-O',str(PLAN/'scan.py')],capture_output=True,timeout=120);need(qopt.returncode==1 and b'optimized Python rejected' in qopt.stderr,'optimized guard')
 print(json.dumps({'status':'PASS_INDEPENDENT_SYMBOLIC_GRAPH_SOURCE_CLOSURE_AUDIT','source_commit':'05cfc83473','later_author_only_exploration_commit':'b2c594d96d','fresh_scan_exit':q.returncode,'optimized_scan_exit':qopt.returncode,'source_modules':modules,'inherited_objects_per_side':127,'low_population_candidates':2,'scope':'Point-in-time source/import/provider scan, not simultaneous freeze or paired build. Both graph-port symbolic equalities and graph/radix hypotheses remain explicit; no retained-port calibration, checker, machine or PRA endpoint.'},indent=2))
if __name__=='__main__':main()
