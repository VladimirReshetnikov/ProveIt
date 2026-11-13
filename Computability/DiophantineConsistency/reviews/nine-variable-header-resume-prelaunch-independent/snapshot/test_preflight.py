#!/usr/bin/env python3
"""Replay the pinned snapshot and test review-gate refusal without Lean."""
import importlib.util
import json
import tempfile
from pathlib import Path
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('launch',here/'launch.py')
launch=importlib.util.module_from_spec(spec);spec.loader.exec_module(launch)
repo=next(p for p in here.parents if (p/'lakefile.toml').is_file())
research=repo/'Computability/DiophantineConsistency/research'
paths=[research/'nine-variable-external-matrix-preflight/header-result.json',research/'nine-variable-current-base-source-survey/result-final.json']
hashes=['7c5751dfd7002b3425e71f462f8058078ee0911e5f4ecbcd1e66871a4832b9fe','7aa788ec612ef2d1cf40e65cf16b507099532477cd581dfe2c560d7b934d31ca']
if [launch.sha(p) for p in paths]!=hashes:raise RuntimeError('snapshot hash mismatch')
prior,survey=[json.loads(p.read_text()) for p in paths]
seeds=sorted(survey['declared_external']);state=launch.core.restore(prior,seeds)
if len(seeds)!=128 or len(prior['modules'])!=64 or len(prior['frontier'])!=199:raise RuntimeError('snapshot count mismatch')
if (here/'review-gate.json').exists():raise RuntimeError('real review gate unexpectedly present')
with tempfile.TemporaryDirectory(prefix='header-resume-gate-test-') as temp:
    gate=Path(temp)/'review-gate.json';hashes=launch.code_hashes()
    def rejected():
        try:launch.review_gate(gate,hashes)
        except (RuntimeError,FileNotFoundError):return True
        return False
    if not rejected():raise RuntimeError('missing gate accepted')
    gate.write_text(json.dumps({'decision':'PASS_PRELAUNCH_REVIEW','reviewer':'synthetic','code_hashes':{}}))
    if not rejected():raise RuntimeError('stale gate accepted')
    gate.write_text(json.dumps({'decision':'PASS_PRELAUNCH_REVIEW','reviewer':'synthetic','code_hashes':hashes}))
    launch.review_gate(gate,hashes)
print(json.dumps({'status':'PASS_STATIC_PREFLIGHT_CONTROLS','prior_modules':len(prior['modules']),
                  'prior_frontier':len(prior['frontier']),'declared_seeds':len(seeds),
                  'resumed_frontier':len(state['queue']),
                  'scope':'Pinned queue replay and synthetic gate controls; no Lean or header traversal.'},sort_keys=True))
