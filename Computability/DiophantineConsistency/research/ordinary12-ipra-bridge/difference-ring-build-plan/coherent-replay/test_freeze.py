#!/usr/bin/env python3
"""Controls for source header parser and topological closure; no project build."""
import importlib.util
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
print('PASS_COHERENT_FREEZER_TOY parser topology external cycle missing')
