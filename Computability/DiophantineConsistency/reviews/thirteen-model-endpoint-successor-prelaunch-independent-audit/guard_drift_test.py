#!/usr/bin/env python3
"""Test actual launcher companion guards against synthetic file drift."""
import hashlib,importlib.util,json,os,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];path=ROOT/'Computability/DiophantineConsistency/research/thirteen-model-endpoint-successor/replay.py'
spec=importlib.util.spec_from_file_location('driver',path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
with tempfile.TemporaryDirectory(prefix='endpoint-companion-controls-') as d:
 p=Path(d)/'a.olean';p.write_text('original');missing=Path(d)/'a.olean.private';h=hashlib.sha256(p.read_bytes()).hexdigest();guard={str(p):{'realpath':str(p.resolve()),'sha256':h},str(missing):None};m.check_guards(guard)
 p.write_text('mutated')
 try:m.check_guards(guard)
 except ValueError:pass
 else:raise ValueError('modified file accepted')
 p.write_text('original');missing.write_text('unexpected')
 try:m.check_guards(guard)
 except ValueError:pass
 else:raise ValueError('unexpected companion accepted')
 missing.unlink();p.unlink()
 try:m.check_guards(guard)
 except ValueError:pass
 else:raise ValueError('missing required companion accepted')
 print(json.dumps({'status':'PASS_SUCCESSOR_COMPANION_DRIFT_CONTROLS','cases':['baseline','modified','unexpected','missing']},indent=2))
