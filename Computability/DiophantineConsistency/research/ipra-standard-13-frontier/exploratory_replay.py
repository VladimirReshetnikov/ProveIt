#!/usr/bin/env python3
"""Compile the standard-theory modules and both 13-variable clients in one overlay."""
import hashlib,json,os,re,shutil,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('assertions required')
D=Path(__file__).resolve().parent
TASK=D.parents[1]
PARENT=Path('/tmp/ipra-aq29-fresh-project-pair/author')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
OUT=Path('/tmp/ipra-standard-13-frontier-exploratory-20261101')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert H(PARENT/'state.json')=='b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153'
old=TASK/'research/adaptive-aq22-proof/author-additions.json'
assert H(old)=='3c5df040f94803b19ccbed14ec93be2e3de2e16ed9c31efd9bcfb531373200df'
spec=json.loads(old.read_text());root=D.parents[3]
names=['IPRASuccessorInduction','IPRAAddOneGeneral','IPRASuccessorInductionConverse','IPRAStandardTheory',
       'AdaptiveDirectOrdinateSquareSumsLiteral','IPRASquareSumsNative','IPRAStandardSquareSums13','IPRAStandardProduct13']
sources=[]
for name in names[:4]:
 row=spec['sources']['DiophantineConsistency.'+name];p=root/row['workspace_path'];assert H(p)==row['sha256'];sources.append(p)
for name in names[4:]:sources.append(D/'draft-src'/(name+'.lean'))
assert H(sources[4])=='9eb21e1febd710884d971be3431387144845d9eb8e6a0747d7224d1321c01a78'
assert H(sources[5])=='09d068c77bc97fa1202401c4d032cd3f835d280cc80ad3b1396d709443f91eee'
assert not OUT.exists();(OUT/'src/DiophantineConsistency').mkdir(parents=True);(OUT/'lib').mkdir();(OUT/'logs').mkdir()
for current,dirs,files in os.walk(PARENT/'lib'):
 source=Path(current);dest=OUT/'lib'/source.relative_to(PARENT/'lib');dest.mkdir(exist_ok=True)
 for name in files:(dest/name).symlink_to(source/name)
env=dict(os.environ,LEAN_PATH=str(OUT/'lib')+':'+str(PACKAGE),LEAN_NUM_THREADS='1')
for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
before={str(p):H(p) for p in sources};rows=[]
for name,source in zip(names,sources):
 dest=OUT/'src/DiophantineConsistency'/source.name;shutil.copyfile(source,dest)
 obj=OUT/'lib/DiophantineConsistency'/(name+'.olean');assert not os.path.lexists(obj)
 p=subprocess.run([str(LEAN),'-M8000','-j1','-DElab.async=false','--root='+str(OUT/'src'),str(dest),'-o',str(obj)],
                  cwd=OUT/'src',env=env,text=True,capture_output=True,timeout=300)
 log=OUT/'logs'/(name+'.log');log.write_text(p.stdout+p.stderr)
 rows.append({'module':name,'source_sha256':H(source),'exit_code':p.returncode,'log_sha256':H(log),
              'object_sha256':H(obj) if obj.is_file() else None})
 print('MODULE',name,'exit',p.returncode,flush=True)
 if p.returncode:raise SystemExit(p.returncode)
assert {str(p):H(p) for p in sources}==before
expected={
 'IPRAStandardSquareSums13': ['DiophantineConsistency.IPRASquareSumsNative.'+x for x in ['sameZero','bridge','equivalence','literal_eq','literal_equivalence']]+['DiophantineConsistency.IPRAStandardSquareSums13.'+x for x in ['literal_equivalence','selected_foundation_consistency','literal_iff_translated_consistency']],
 'IPRAStandardProduct13': ['DiophantineConsistency.HAAdaptiveDirectOrdinate86.polynomialBridge']+['DiophantineConsistency.IPRAStandardProduct13.'+x for x in ['native_equivalence','literal_equivalence','selected_foundation_consistency','literal_iff_translated_consistency']]
}
for module,names_expected in expected.items():
 last=(OUT/'logs'/(module+'.log')).read_text()
 reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",last,re.M)
 assert [name for name,_ in reports]==names_expected
 for _,axioms in reports:assert set(filter(None,re.split(r'\s*,\s*',axioms.strip()))) <= {'propext','Classical.choice','Quot.sound'}
evidence=D/'exploratory';evidence.mkdir(exist_ok=False)
shutil.copytree(OUT/'logs',evidence/'logs')
receipt={'status':'PASS_13_FRONTIER_EXPLORATORY','rows':rows,'diagnostic_names':expected,
         'parent_state_sha256':H(PARENT/'state.json'),'lean_sha256':H(LEAN),'overlay':str(OUT),
         'scope':'Exploratory single-author AQ29-parent overlay; no full pre/post guards, independent replay, matched extension or current-source claim.'}
(evidence/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print('PASS_13_FRONTIER_EXPLORATORY',H(evidence/'receipt.json'))
