#!/usr/bin/env python3
"""Independent corrected freezer path and precreation controls; no real freeze."""
import contextlib,hashlib,importlib.util,io,json,subprocess,sys,tempfile
from pathlib import Path
from unittest.mock import patch
if not __debug__:raise RuntimeError('assertions required')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];TASK=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/difference-ring-build-plan/coherent-replay'
if len(sys.argv)!=2:raise ValueError('pass exact committed correction')
commit=sys.argv[1];path=TASK/'freeze.py';raw=subprocess.check_output(['git','show',commit+':'+str(path.relative_to(ROOT))],cwd=ROOT);assert raw==path.read_bytes()
def rejected(fn):
 try:fn()
 except ValueError:return
 raise AssertionError('unsafe output accepted')
with tempfile.TemporaryDirectory(prefix='ipra-freezer-corrected-review-') as td:
 top=Path(td);fixture=top/'a/b/c/d/e/f';fixture.mkdir(parents=True);mod=fixture/'freeze.py';mod.write_bytes(raw);spec=importlib.util.spec_from_file_location('corrected_freezer_review',mod);f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
 safe=top/'safe';safe.mkdir();protected=top/'protected';protected.mkdir();link=top/'link';link.symlink_to(safe,target_is_directory=True)
 assert f.validate_output(safe/'new',[protected])==(safe/'new').resolve()
 rejected(lambda:f.validate_output(protected/'nested',[protected]))
 rejected(lambda:f.validate_output(top/'fresh-ancestor',[top/'fresh-ancestor/protected']))
 rejected(lambda:f.validate_output(link/'nested',[protected]))
 rejected(lambda:f.validate_output(safe/'x/../other',[protected]))
 rejected(lambda:f.validate_output(protected,[protected]))
 bad=top/'broken';bad.symlink_to(top/'missing');rejected(lambda:f.validate_output(bad,[protected]))
 # Source-walk fixture creates the previously absent output after first check;
 # the real main must reject at its second pre-creation guard.
 fake=top/'checkout';fake.mkdir();(fake/'lakefile.toml').write_text('lean_lib = []\n');(fake/'lean-toolchain').write_text('toy\n');(fake/'Source.lean').write_text('def toy := 0\n');f.ROOT=fake
 target=f.TARGET;names=['P.M'+str(i) for i in range(69)]+[target];blob=(fake/'Source.lean').read_bytes();fake_rows={n:{'path':'Source.lean','raw':blob,'imports':[]} for n in names};dest=safe/'raced'
 def race(*args):dest.mkdir();return fake_rows,names,[]
 with patch.object(f,'walk',race),patch.object(f.subprocess,'check_output',return_value='fixture-head\n'),patch.object(sys,'argv',['freeze.py','--output',str(dest)]),contextlib.redirect_stdout(io.StringIO()):rejected(f.main)
 assert not (dest/'manifest.json').exists() and not (dest/'src').exists()
 # After the first source's per-copy check succeeds, mutate that source while
 # the second is being copied. The final all-source rehash must reject it.
 distinct={}
 for i,name in enumerate(names):
  file=fake/('Source'+str(i)+'.lean');file.write_text('def toy := '+str(i)+'\n');distinct[name]={'path':file.name,'raw':file.read_bytes(),'imports':[]}
 drift=safe/'drift';source0=fake/'Source0.lean';original_hash=f.H;did_change=[False]
 def drifting_hash(p):
  p=Path(p)
  if p==drift/'src/P/M1.lean' and not did_change[0]:source0.write_text('def changed := 1\n');did_change[0]=True
  return original_hash(p)
 with patch.object(f,'walk',return_value=(distinct,names,[])),patch.object(f.subprocess,'check_output',return_value='fixture-head\n'),patch.object(f,'H',drifting_hash),patch.object(sys,'argv',['freeze.py','--output',str(drift)]),contextlib.redirect_stdout(io.StringIO()):
  try:f.main()
  except ValueError as e:assert 'source drift before manifest' in str(e)
  else:raise AssertionError('source drift accepted')
 assert did_change[0] and not (drift/'manifest.json').exists()
result={'status':'PASS_INDEPENDENT_CORRECTED_FREEZER_CONTROLS','commit':commit,'source_sha256':hashlib.sha256(raw).hexdigest(),'nested_overlap_rejected':True,'ancestor_overlap_rejected':True,'symlink_ancestor_rejected':True,'noncanonical_ancestor_rejected':True,'broken_target_rejected':True,'precreation_race_rejected':True,'post_copy_source_drift_rejected':True,'scope':'Toy paths and one controlled check-before-mkdir race only; not a guarantee against adversarial path replacement during filesystem writes.'};out=HERE/'corrected-receipt.json'
if out.exists():raise ValueError('refusing overwrite')
out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(result['status'],hashlib.sha256(out.read_bytes()).hexdigest())
