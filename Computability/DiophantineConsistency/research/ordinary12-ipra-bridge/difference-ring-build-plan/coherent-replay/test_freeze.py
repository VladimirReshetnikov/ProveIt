#!/usr/bin/env python3
"""Controls for source header parser and topological closure; no project build."""
import importlib.util
import subprocess
import sys
import tempfile
from pathlib import Path
p=Path(__file__).with_name('freeze.py');spec=importlib.util.spec_from_file_location('freeze',p);f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
assert f.imports(b'/- import Hidden\n /- nested -/ -/\nimport A.B -- x\npublic import C.D\n')==['A.B','C.D']
for bad in (b'/- unclosed',b'import Bad;evil\n'):
 try:f.imports(bad)
 except ValueError:pass
 else:raise AssertionError('invalid header accepted')
files={'P.Target':b'import P.A\nimport X.Ext\n','P.A':b'import P.B\n','P.B':b'def b := 1\n'}
def read(n):
 if n not in files:raise FileNotFoundError(n)
 return n,files[n]
rows,order,ext=f.walk('P.Target',read,lambda n:n.startswith('P.'))
assert order==['P.B','P.A','P.Target'] and ext==['X.Ext'] and len(rows)==3
files['P.B']=b'import P.Target\n'
try:f.walk('P.Target',read,lambda n:n.startswith('P.'))
except ValueError as e:assert 'cycle' in str(e)
else:raise AssertionError('cycle accepted')
del files['P.B']
try:f.walk('P.Target',read,lambda n:n.startswith('P.'))
except FileNotFoundError:pass
else:raise AssertionError('missing project source accepted')
with tempfile.TemporaryDirectory() as td:
 root=Path(td);protected=root/'protected';protected.mkdir()
 safe=root/'safe';safe.mkdir()
 assert f.validate_output(safe/'new',[protected])==safe/'new'
 for output,guards in ((protected/'child',[protected]),
                       (root/'newparent',[root/'newparent'/'nested']),
                       (protected,[protected])):
  try:f.validate_output(output,guards)
  except ValueError:pass
  else:raise AssertionError('protected overlap/existing output accepted')
 (root/'symlink').symlink_to(safe,target_is_directory=True)
 try:f.validate_output(root/'symlink'/'new',[protected])
 except ValueError:pass
 else:raise AssertionError('symlink ancestor accepted')
 try:f.validate_output(safe/'..'/'escaped',[protected])
 except ValueError:pass
 else:raise AssertionError('noncanonical ancestor accepted')
 forbidden=f.ROOT/'__coherent_freeze_must_not_create__'
 assert not forbidden.exists() and not forbidden.is_symlink()
 run=subprocess.run([sys.executable,str(p),'--output',str(forbidden)],capture_output=True,text=True)
 assert run.returncode!=0 and 'output/protected overlap' in run.stderr and not forbidden.exists()
 evidence=Path('/tmp/ipra-ordinary12-coexistence-source-01/__must_not_create__')
 assert not evidence.exists() and not evidence.is_symlink()
 run=subprocess.run([sys.executable,str(p),'--output',str(evidence)],capture_output=True,text=True)
 assert run.returncode!=0 and 'output/protected overlap' in run.stderr and not evidence.exists()
 newer=Path('/tmp/ipra-ordinary12-coexistence-source-02/__must_not_create__')
 if newer.parent.is_dir():
  assert not newer.exists() and not newer.is_symlink()
  run=subprocess.run([sys.executable,str(p),'--output',str(newer)],capture_output=True,text=True)
  assert run.returncode!=0 and 'output/protected overlap' in run.stderr and not newer.exists()
print('PASS_COHERENT_FREEZER_TOY parser topology external cycle missing overlap symlink canonical')
