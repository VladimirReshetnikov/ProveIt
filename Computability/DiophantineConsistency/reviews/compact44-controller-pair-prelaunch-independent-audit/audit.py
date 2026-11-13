#!/usr/bin/env python3
"""No-Lean exact-byte, warning-inventory and fake-controller-wrapper review."""
import hashlib,importlib.util,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];HERE=Path(__file__).resolve().parent;DRIVER=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-controller-pair-prototype/replay.py';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();D='bea24a34e875a7b3b8a6de47b1982609449d528aeed8cca9ddfda5961a28b753'
assert H(DRIVER)==D
rel=DRIVER.relative_to(ROOT).as_posix();old=subprocess.run(['git','show','4cfd4ee4f8:'+rel],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(old).hexdigest()==D
sp=importlib.util.spec_from_file_location('candidate',DRIVER);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
for p,h in m.PINS.items():assert H(p)==h,('input pin',str(p))
expected=[['g_mod_nat','zc_surj','zc_inj'],['controller_choice','rank_calibration']];counts=[1,2];inventories=[]
for ix,path in enumerate(m.OBS):
 text=m.observed_expected(path);reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.M);typ=('Data','Choice')[ix];prefix='DiophantineConsistency.ArithmeticController'+typ+'Compact44.'
 assert text.count('warning:')==counts[ix] and [n for n,_ in reports]==[prefix+n for n in expected[ix]]
 assert all({v.strip() for v in a.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,a in reports)
 assert '<SOURCE>:' in text and 'sorryAx' not in text and 'error:' not in text
 inventories.append({'module':typ,'warnings':counts[ix],'named_reports':[n for n,_ in reports]})
q=subprocess.run([sys.executable,'-I','-S','-B',str(HERE/'fake-wrapper.py')],cwd=ROOT,capture_output=True,text=True,timeout=120)
if q.returncode or q.stderr:raise ValueError(('fake wrapper failed',q.returncode,q.stderr,q.stdout))
lines=q.stdout.strip().splitlines();assert len(lines)==19 and lines[0]=='good PASS 4 fake children' and all(' PASS ' in x for x in lines)
print(json.dumps({'status':'PASS_INDEPENDENT_CONTROLLER_PRELAUNCH_FAKE_REVIEW','driver_commit':'4cfd4ee4f8','driver_sha256':D,'fixed_pins_checked':len(m.PINS),'observed_output_inventories':inventories,'fake_cases':lines,'lean_launched':False,'scope':'No-Lean exact-byte, full-output warning/axiom inventory and fake wrapper; actual contextual preflight separately observed. Real build untested, clean initial loader, stable HEAD, sole Lean, sampled monitor and dependency-query/package/between-check limits apply.'},indent=2))
