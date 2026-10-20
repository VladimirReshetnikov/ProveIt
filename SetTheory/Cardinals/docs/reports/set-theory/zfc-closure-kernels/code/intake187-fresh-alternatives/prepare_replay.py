from pathlib import Path, PurePosixPath
import argparse,hashlib,io,json,shutil,stat,zipfile
ap=argparse.ArgumentParser(description='Prepare the14 reviewed Source141 direct jobs on a fresh copy; do not execute supplied code.')
ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--output-dir',type=Path,required=True);a=ap.parse_args()
P=a.packet.resolve();E=a.output_dir.resolve()
assert P.is_dir() and P!=E and P not in E.parents
assert not any(x.is_symlink() for x in P.rglob('*'))
assert not E.exists(); E.mkdir()
C=E/'packet';shutil.copytree(P,C,symlinks=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
archive=C/'vendor/K219_Construction_2026-10-20.zip'
assert sha(archive)=='04813567f393b6c4015a96aba092159e9021703b4b662c7be69bd2a86497e31b'
base_dir=E/'recovered';base_dir.mkdir();seen=set()
with zipfile.ZipFile(archive) as z:
 for m in z.infolist():
  p=PurePosixPath(m.filename)
  assert not p.is_absolute() and '..' not in p.parts and p.parts[0]=='K219_Construction_2026-10-20'
  assert not any(c in m.filename for c in ('\\',':','\0')) and str(p) not in seen
  assert stat.S_IFMT(m.external_attr>>16) in (0,stat.S_IFDIR,stat.S_IFREG) and not m.flag_bits&1
  seen.add(str(p)); dst=base_dir.joinpath(*p.parts)
  if m.is_dir():dst.mkdir(parents=True,exist_ok=True)
  else:
   dst.parent.mkdir(parents=True,exist_ok=True)
   with z.open(m) as src,dst.open('xb') as out:shutil.copyfileobj(src,out)
   assert dst.stat().st_size==m.file_size
B=base_dir/'K219_Construction_2026-10-20'
V=E/'runtime-vendor';V.mkdir()
ancestor=B/'portable/vendor/K220_Construction_2026-10-20.zip'
assert sha(ancestor)=='132cbb326fcbf6e54957a03095c5f790e207f4ed8ebfb6ceb6e272f329e4ee00'
with zipfile.ZipFile(ancestor) as z:
 names=[n for n in z.namelist()if n.endswith('/K221_Construction_2026-10-20.zip')];assert len(names)==1
 raw=z.read(names[0])
assert hashlib.sha256(raw).hexdigest()=='a06c99b775193d9642a2734b7dd5fe7b72736fbdf9d9d8be438321d5e5d57ba4'
def nested_member(tail):
 with zipfile.ZipFile(io.BytesIO(raw)) as z:
  names=[n for n in z.namelist()if n.endswith('/'+tail)];assert len(names)==1
  return z.read(names[0])
pins={'symbolic_runtime.py':'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145','independent_runtime.py':'0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'}
for name,h in pins.items():
 data=nested_member('portable/runtime/vendor/'+name);assert hashlib.sha256(data).hexdigest()==h
 (V/name).write_bytes(data)
M=E/'legacy_mapping.json';M.write_bytes(nested_member('portable/runtime/reference_results/legacy_mapping.json'))
assert sha(M)=='26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf'
O=E/'output';O.mkdir();(E/'logs').mkdir();(E/'scratch').mkdir();machines=O/'machine';cert=O/'certificates'
for n in ('zero_terminal','retagged','composed'):(cert/n).mkdir(parents=True)
jobs=[]
def job(name,args,timeout=60):jobs.append(dict(name=name,argv=['python3','-B',*map(str,args)],timeout_seconds=timeout,cwd=str(C)))
job('01_construct',[C/'portable/construct.py','--baseline',B,'--output',machines])
args=[C/'verification/independent_source_check.py']
inputs={'original-source':B/'machine/sites219.json','zero-source':machines/'zero_terminal/sites.json','retagged-source':machines/'retagged/sites.json','retagged-seed-source':machines/'retagged/sites.json','combined-source':machines/'composed/sites.json','original-table':B/'machine/k219.native.tm','zero-table':machines/'zero_terminal/k219.native.tm','retagged-table':machines/'retagged/k219.native.tm','retagged-seed-table':machines/'composition_seed.tm','combined-table':machines/'composed/k219.native.tm','combined-native-table':C/'machine/composed/k219.upstream-labels.tm'}
for k,v in inputs.items():args += ['--'+k,v]
job('02_independent_source',[*args,'--output-dir',O/'independent-source'])
for n in ('zero_terminal','retagged','composed'):
 job('03_source_'+n,[C/'portable/check_source.py','--baseline',B,'--source',machines/n/'sites.json','--variant',n,'--output',cert/n/'source.json'])
 job('04_canonical_'+n,[C/'portable/canonicalize.py','--variant',n,'--table',machines/n/'k219.native.tm','--source',machines/n/'sites.json','--output',machines/n])
job('05_independent_small',[C/'verification/independent_small_audit.py','--release',C,'--baseline',B,'--out',O/'independent-small'])
for n in ('zero_terminal','retagged','composed'):
 job('06_runtime_'+n,[C/'portable/check_runtime.py','--variant',n,'--table',machines/n/'k219.native.tm','--source',machines/n/'sites.json','--vendor',V,'--mapping',M,'--out',cert/n],180)
job('07_independent_runtime',[C/'verification/independent_runtime_audit.py','--release',C,'--zero',cert/'zero_terminal','--retagged',cert/'retagged','--composed',cert/'composed','--out',O/'independent-runtime.json'])
job('08_negative_controls',[C/'verification/negative_controls.py','--baseline',B,'--vendor',V,'--certificates',cert,'--output',O/'negative-controls.json'])
selected=[C/'portable'/n for n in ('construct.py','check_source.py','check_runtime.py','canonicalize.py','reproduce.py')]+[C/'verification'/n for n in ('independent_source_check.py','independent_small_audit.py','independent_runtime_audit.py','negative_controls.py')]+[V/n for n in pins]+[M,archive,C/'machine/construction.json',B/'machine/k219.native.tm',B/'machine/sites219.json']
plan=dict(status='PREPARED_PORTABLE_DIRECT_LEAF_PLAN',role='opening_encoder portable adaptation of actually executed14-job source-reviewed plan; preparation is not a proof execution',packet=str(C),pristine=str(P),baseline=str(B),recovered_archive_members=len(seen),inputs={str(p):sha(p) for p in selected},jobs=jobs,scope='Fresh source reconstruction, complete source/CFG transport, finite complete blank startups, three full unbounded symbolic primitive checks, independent receipt/block audit and malformed-input controls. No manifest/checksum suite, delivered wrapper, inherited suite, Coq/Rocq/Lean invocation. Inherited logical calibration not freshly replayed.')
(E/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
print(json.dumps({'jobs':len(jobs),'baseline_members':len(seen),'plan':str(E/'plan.json'),'plan_sha256':sha(E/'plan.json')},indent=2))
