#!/usr/bin/env python3
"""Independently check a source-only join frontier; never launches Lean."""
import hashlib,json,os,pathlib,re,subprocess,sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('isolated, nonoptimized Python required')
root=pathlib.Path.cwd();base=root/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-direct-k-band-join-plan';H=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def git_blob(rev,p):
 r=subprocess.run(['git','show',rev+':'+p.relative_to(root).as_posix()],cwd=root,capture_output=True,check=True,timeout=60);return hashlib.sha256(r.stdout).hexdigest()
scanfile=base/'scan.json'; h='2048ee458a2f49755858e991e3837b71aab244ce9c8521e483e6cdea6282616d'
if H(scanfile)!=h or git_blob('2a0893db3c',scanfile)!=h:raise ValueError('plan bytes differ')
s=json.loads(scanfile.read_bytes());rows=s['source_order'];names=[r['module'] for r in rows]
if len(rows)!=14 or len(set(names))!=14:raise ValueError('source count')
expected_external={'DiophantineConsistency.ArithmeticWindowDigits','DiophantineConsistency.Compact943Data','DiophantineConsistency.CompactCoefficientMass','Mathlib.Algebra.BigOperators.Ring.Finset'}
external=set();available=set();out=[]
for r in rows:
 p=pathlib.Path(r['source']);text=p.read_text();imports=[x[7:] for x in text.splitlines() if x.startswith('import ')];reports=re.findall(r'^#print axioms\s+(\S+)',text,re.M)
 if H(p)!=r['source_sha256'] or git_blob(r['source_commit'],p)!=r['source_sha256'] or imports!=r['imports'] or reports!=r['axiom_reports']:raise ValueError(('source drift',str(p)))
 for dep in imports:
  if dep not in available:
   if dep in names:raise ValueError(('forward source dependency',dep))
   external.add(dep)
 available.add(r['module']);out.append({'module':r['module'],'sha256':r['source_sha256'],'imports':imports,'reports':reports})
if external!=expected_external:raise ValueError(('external imports',external))
prefix=pathlib.Path('/tmp/ipra-direct-symbolic-k-pair-01');other=pathlib.Path('/tmp/ipra-compact-coefficient-decomposition-pair-01');diffs={}
expected={'DiophantineConsistency/'+x+'.olean' for x in ('ArithmeticBinaryCarry','ArithmeticBinomLegendre','Compact943Data','CompactCoefficientMass')}
for side in ('author','peer'):
 lib=prefix/side/'lib';lib2=other/side/'lib';p={x.relative_to(lib).as_posix():x for x in lib.rglob('*.olean') if x.is_file()};q={x.relative_to(lib2).as_posix():x for x in lib2.rglob('*.olean') if x.is_file()}
 if len(p)!=150 or len(q)!=126 or len(p.keys()&q.keys())!=90:raise ValueError(('inventory count',side))
 recorded={r['path']:r for r in s['parent_objects'][side]}
 if set(recorded)!=set(p):raise ValueError(('parent paths',side))
 for n,path in p.items():
  r=recorded[n]
  if H(path)!=r['sha256'] or str(path.resolve())!=r['realpath']:raise ValueError(('parent drift',side,n))
 diffs[side]=[{'path':n,'direct_k_sha256':H(p[n]),'coefficient_sha256':H(q[n])} for n in sorted(p.keys()&q.keys()) if H(p[n])!=H(q[n])]
 if {x['path'] for x in diffs[side]}!=expected or diffs[side]!=s['divergent_overlap'][side]:raise ValueError(('divergence mismatch',side))
for k,expected_count in (('external_direct_slots',60),('target_slots',280),('package_slots',20)):
 if len(s[k])!=expected_count:raise ValueError(('slot count',k))
 for name,v in s[k].items():
  p=pathlib.Path(name)
  if v is None:
   if os.path.lexists(p):raise ValueError(('unexpected companion',name))
  elif not p.is_file() or H(p)!=v['sha256'] or str(p.resolve())!=v['realpath']:raise ValueError(('companion drift',name))
if any(v is not None for v in s['target_slots'].values()):raise ValueError('target slot present')
ob=json.loads((base/'terminal-observation.json').read_bytes())
if ob['scan_sha256']!=h or ob['normal_observed_exit']!=0 or ob['optimized_observed_exit']!=1 or ob['lean_launched'] is not False:raise ValueError('terminal observation')
print(json.dumps({'status':'PASS_INDEPENDENT_SOURCE_ONLY_DIRECT_K_BAND_JOIN_REVIEW','source_commit':'2a0893db3c','scan_sha256':h,'source_order':out,'external_imports':sorted(external),'parent_objects_per_side':150,'other_objects_per_side':126,'common_objects_per_side':90,'divergent_overlap':diffs,'slot_counts':{k:len(s[k]) for k in ('external_direct_slots','target_slots','package_slots')},'lean_launched':False,'scope':'Point-in-time source/provider check; no Lean build, parent-audit rerun, model K cast, temporal alignment or retained-byte binding.'},indent=2,sort_keys=True))
