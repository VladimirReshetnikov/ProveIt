#!/usr/bin/env python3
"""Independent point-in-time 12-module source closure and choice review."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';RESEARCH=BASE/'research/ordinary12-ipra-bridge';PLAN=RESEARCH/'free-j-concrete-digits-closure-plan';CLIENT=RESEARCH/'free-j-concrete-digits-client-prototype/FreeJConcreteDigitsClient.lean'
PARENT=BASE/'reviews/ordinary12-freej-saturation-client-independent-audit';PREFIX=Path('/tmp/ipra-freej-saturation-client-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 files=[*(PLAN/x for x in ('README.md','scan.py','scan.json')),CLIENT]
 for p in files:
  name=p.relative_to(ROOT).as_posix();blob=subprocess.run(['git','show','b8dd85dd7d:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+name)
 normal=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,timeout=60);opt=subprocess.run([sys.executable,'-O','-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,timeout=60)
 need(normal.returncode==0 and not normal.stderr and normal.stdout==(PLAN/'scan.json').read_bytes(),'normal scan')
 need(opt.returncode!=0 and b'optimized Python rejected' in opt.stderr,'optimized guard')
 scan=json.loads(normal.stdout);need(scan['status']=='PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD','scan status')
 rows=scan['modules'];need(len(rows)==12 and rows[-1]['module']=='DiophantineConsistency.CompactConcreteIncrement','12 module target')
 parent=json.loads((PARENT/'CHECK.json').read_bytes());need(sha(PARENT/'CHECK.json')=='847f3e467e93d871087695ee3c66f8042c22767a7d43ec1a14973cffe6ee043f' and parent['status']=='PASS_INDEPENDENT_FREEJ_SATURATION_CLIENT_AUDIT' and parent['recorded_outer_exit']==0,'parent receipt')
 sources={}
 for loc in (BASE/'Lean/DiophantineConsistency',RESEARCH):
  for p in loc.rglob('*.lean'):sources.setdefault(p.stem,[]).append(p)
 selected={'CompactDummyBound':('compact44-dummy-bound-prototype','compact44-dummy-bound-independent-audit'),'CompactMaskSlot':('compact44-mask-slot-prototype','compact44-mask-slot-independent-audit')}
 choices={}
 for name,(folder,auditname) in selected.items():
  wanted=RESEARCH/folder/(name+'.lean');choice=scan['explicit_choices'][name];candidates=[{'path':str(p),'sha256':sha(p)} for p in sorted(sources[name])]
  need(choice['selected']==str(wanted) and choice['selected_sha256']==sha(wanted) and choice['all_candidates']==candidates and len(candidates)==2,'ambiguous source choices '+name)
  check=json.loads((BASE/'reviews'/auditname/'CHECK.json').read_bytes());need(check['recorded_outer_exit']==0 and all(row['source_sha256']==sha(wanted) for row in check['runs']),'selected independent audit '+name)
  choices[name]={'selected':str(wanted),'selected_sha256':sha(wanted),'candidate_hashes':[x['sha256'] for x in candidates]}
 lookup={x['module']:x for x in rows};leaf_counts={}
 for side in ('author','peer'):
  lib=PREFIX/side/'lib';objs={str(p.relative_to(lib)):p for p in lib.rglob('*.olean')};records=scan['inherited_objects'];need(len(objs)==len(records)==114 and set(objs)=={x['module_path'] for x in records},'provider inventory')
  for row in records:
   p=objs[row['module_path']];need(sha(p)==row['sha256'] and str(p.resolve())==row[side+'_resolved_path'],'provider object '+row['module_path'])
  seen=set();order=[];leaves=set()
  def visit(n):
   if n in seen:return
   seen.add(n);rel=Path(*n.split('.')).with_suffix('.olean')
   if (lib/rel).is_file() or (PACKAGE/rel).is_file():leaves.add(n);return
   need(n in lookup,'unresolved '+n);row=lookup[n];stem=n.rsplit('.',1)[1]
   candidates=[RESEARCH/selected[stem][0]/(stem+'.lean')] if stem in selected else sources.get(stem,[])
   need(len(candidates)==1 and str(candidates[0])==row['source'] and sha(candidates[0])==row['source_sha256'],'source '+n)
   lines=candidates[0].read_text().splitlines();need(not any(re.match(r'^\s+import\s',l) for l in lines),'indented import')
   imports=[x for l in lines if l.startswith('import ') for x in l[7:].split()];need(imports==row['imports'],'imports '+n)
   for d in imports:visit(d)
   order.append(n)
  visit('DiophantineConsistency.CompactConcreteIncrement')
  need(order==[x['module'] for x in rows] and set(order)==set(lookup),'closure order/reachability');leaf_counts[side]=len(leaves)
 for p in files:
  name=p.relative_to(ROOT).as_posix();blob=subprocess.run(['git','show','b8dd85dd7d:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(blob).hexdigest()==sha(p),'post-check drift '+name)
 print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_CONCRETE_DIGITS_SOURCE_CLOSURE_AUDIT','source_commit':'b8dd85dd7d','normal_scan_exit':normal.returncode,'optimized_scan_exit':opt.returncode,'inherited_objects_per_side':114,'modules':[r['module'] for r in rows],'explicit_choices':choices,'leaf_counts':leaf_counts,'scope':'Point-in-time source closure and explicitly uncompiled client only; no simultaneous freeze, coherent compilation, retained-MC/graph equality, package/dynamic ancestry or PRA theorem.'},indent=2))
if __name__=='__main__':main()
