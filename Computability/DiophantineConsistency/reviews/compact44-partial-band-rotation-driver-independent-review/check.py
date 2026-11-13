#!/usr/bin/env python3
"""Read-only byte/guard inventory and fake controls; never launches Lean."""
import hashlib, importlib.util, json, os, pathlib, subprocess, sys
P=pathlib.Path.cwd()/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-partial-band-rotation-pair-prototype'
H=lambda p: hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
if not sys.flags.isolated or not sys.flags.no_site or not __debug__ or os.environ.get('PYTHONOPTIMIZE'): raise ValueError('isolated nonoptimized Python required')
D=P/'replay.py'; expected='048bffe62ac8ff6cff4793f64e54008d9b6f592ac732d08ab55fbb9c6fe2fdd8'
if H(D)!=expected: raise ValueError('driver mismatch')
spec=importlib.util.spec_from_file_location('reviewed_driver',D); d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d)
d.validate_provider()
for p,h in d.PINS.items():
 if not p.is_file() or H(p)!=h: raise ValueError(('fixed pin mismatch',str(p)))
scan=json.loads((d.PLAN/'scan.json').read_bytes()); rows=[]
for key in ('first_source','second_source'):
 r=scan[key];p=pathlib.Path(r['source']); imports=[l[7:] for l in p.read_text().splitlines() if l.startswith('import ')]
 if not p.is_file() or H(p)!=r['sha256'] or imports!=r['imports']:raise ValueError(('source mismatch',key))
 rows.append({'module':r['module'],'sha256':r['sha256'],'imports':imports,'realpath':str(p.resolve())})
if [x['module'] for x in rows]!=d.MODULES:raise ValueError('source order')
want={'DiophantineConsistency.CompactPartialBand':{'CompactPartialBand.band_decomposition'},'DiophantineConsistency.CompactPartialBandRotation':{'CompactPartialBandRotation.band_rotation_congr','CompactPartialBandRotation.band_column'}}
if d.REPORTS!=want or d.AXIOMS!={'propext','Classical.choice','Quot.sound'}:raise ValueError('wrong reports')
if len(d.SUFFIXES)!=10 or len(set(d.SUFFIXES))!=10:raise ValueError('companion inventory')
fake=json.loads((P/'fake-observation.json').read_bytes());pre=json.loads((P/'preflight-observation.json').read_bytes())
if fake['driver_sha256']!=expected or fake['controls_sha256']!=H(P/'fake-controls.py') or fake['log_sha256']!=H(P/'fake-controls.log') or fake['observed_exit']!=0 or fake['lean_launched'] is not False:raise ValueError('fake observation')
if pre['driver_sha256']!=expected or pre['stdout_sha256']!=H(P/'preflight.json') or pre['observed_exit']!=0 or pre['lean_launched'] is not False or pre['stderr_bytes']!=0:raise ValueError('preflight observation')
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'fake-controls.py')],capture_output=True,timeout=120)
if r.returncode!=0 or r.stderr or r.stdout!=(P/'fake-controls.log').read_bytes():raise ValueError(('fake rerun',r.returncode,r.stderr))
print(json.dumps({'status':'PASS_NO_LEAN_INDEPENDENT_PARTIAL_BAND_DRIVER_REVIEW','driver_sha256':expected,'source_rows':rows,'provider':str(d.PREFIX),'fixed_pin_count':len(d.PINS),'suffixes':list(d.SUFFIXES),'report_names':{k:sorted(v) for k,v in want.items()},'axioms':sorted(d.AXIOMS),'fake_controls_exit':r.returncode,'fake_log_sha256':hashlib.sha256(r.stdout).hexdigest(),'recorded_preflight_head':pre['head'],'recorded_preflight_sha256':pre['stdout_sha256'],'lean_launched':False,'scope':'Source and guard inventory plus fake controls; does not launch Lean, independently rerun parent audits or establish a paired artifact.'},indent=2,sort_keys=True))
