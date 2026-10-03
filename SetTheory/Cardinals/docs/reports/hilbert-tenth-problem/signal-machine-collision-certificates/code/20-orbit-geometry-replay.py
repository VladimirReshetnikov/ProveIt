#!/usr/bin/env python3
"""Run finite checks in isolated copies with exact typed receipt comparison."""
from pathlib import Path
import argparse, hashlib, json, shutil, stat, subprocess, sys, tempfile
ROOT = Path(__file__).resolve().parent

def fail(message):
    raise RuntimeError(message)

def typed_equal(actual, expected, label='receipt'):
    if type(actual) is not type(expected):
        fail(label + ': type mismatch')
    if isinstance(expected, dict):
        if set(actual) != set(expected):
            fail(label + ': key mismatch')
        for key in expected:
            typed_equal(actual[key], expected[key], label + '.' + key)
    elif isinstance(expected, list):
        if len(actual) != len(expected):
            fail(label + ': length mismatch')
        for i, (a,b) in enumerate(zip(actual,expected)):
            typed_equal(a,b,label+'['+str(i)+']')
    elif actual != expected:
        fail(label + ': value mismatch')

def snapshot():
    out={}
    for p in sorted(ROOT.rglob('*')):
        if p.is_symlink():
            fail('Release contains symlink')
        if p.is_file():
            st=p.stat()
            out[p.relative_to(ROOT).as_posix()] = (hashlib.sha256(p.read_bytes()).hexdigest(),stat.S_IMODE(st.st_mode),st.st_mtime_ns)
    return out

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--output-dir',required=True,type=Path)
a=p.parse_args()
out=a.output_dir.resolve()
if out==ROOT or ROOT in out.parents:
    fail('Replay output directory must be external to the release')
if out.exists() and any(out.iterdir()):
    fail('Output directory must be absent or empty')
out.mkdir(parents=True,exist_ok=True)
before=snapshot()
expected={label:json.loads((ROOT/'verification'/('expected-'+label+'.json')).read_text()) for label in ('geometry','examples','first-visit')}
# Explicit schema gates supplement recursive exact type/value equality.
g=expected['geometry']
if type(g.get('receipt_type')) is not str or g['receipt_type']!='sparse_orbit_geometry_audit' or type(g.get('schema_version')) is not int or g['schema_version']!=1:
    fail('Geometry receipt schema mismatch')
if type(g.get('both_rule_variants')) is not bool or g['both_rule_variants'] is not True:
    fail('Geometry boolean schema mismatch')
for label in ('geometry','examples'):
    if expected[label].get('status')!='passed':
        fail(label+' expected receipt not passed')
for key in ('malformed_configurations_checked','drift_box_formulas_checked','exact_physical_time_counts_checked','horizontal_inverse_counts_checked'):
    if type(expected['examples'].get(key)) is not int or expected['examples'][key]<=0:
        fail('Example integer schema mismatch: '+key)
for key,value in expected['first-visit'].items():
    if key!='limitations' and (type(value) is not int or value<0):
        fail('First-visit integer schema mismatch: '+key)
if type(expected['first-visit'].get('limitations')) is not str:
    fail('First-visit limitations schema mismatch')
commands={'geometry':'geometry/audit.py','examples':'examples/independent-audit.py','first-visit':'first-visit/audit.py'}
records={}
for mode,flags in (('normal',[]),('optimized',['-O'])):
    with tempfile.TemporaryDirectory(prefix='report30-'+mode+'-') as tmp:
        work=Path(tmp)
        shutil.copytree(ROOT/'scientific',work/'scientific',copy_function=shutil.copy2)
        records[mode]={}
        for label,relative in commands.items():
            done=subprocess.run([sys.executable,'-I','-B',*flags,str(work/'scientific'/relative)],cwd=work,text=True,capture_output=True)
            if done.returncode:
                fail(label+' '+mode+' failed: '+done.stderr)
            actual=json.loads(done.stdout)
            typed_equal(actual,expected[label],label+' '+mode)
            records[mode][label]=actual
            (out/(label+'-'+mode+'.json')).write_text(json.dumps(actual,indent=2,sort_keys=True)+'\n')
            (out/(label+'-'+mode+'.log')).write_text(done.stdout+done.stderr)
typed_equal(records['normal'],records['optimized'],'normal versus optimized')
probe=json.loads(json.dumps(expected['geometry']))
probe['schema_version']=True
try:
    typed_equal(probe,expected['geometry'],'boolean versus integer regression')
except RuntimeError:
    type_probe='PASS'
else:
    fail('A boolean was incorrectly accepted as integer one')
if snapshot()!=before:
    fail('Release bytes, modes, or modification times changed')
summary={'status':'PASS','normal_optimized_exact_typed_equality':True,'payload_bytes_modes_mtimes_preserved':True,'boolean_integer_type_regression':type_probe,'checks':['geometry','examples','first-visit'],'scope':'Finite checks only; unrestricted conclusions depend on the mathematical proofs'}
(out/'replay-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
