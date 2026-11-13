#!/usr/bin/env python3
"""Read-only controller replay input verification; never launches Lean."""
import argparse,importlib.util,json,os,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke with python3 -I -S, without optimization')
p=Path(__file__).resolve().parent/'replay.py';spec=importlib.util.spec_from_file_location('controller_replay',p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
ap=argparse.ArgumentParser();ap.add_argument('--historical-view',type=Path,required=True);a=ap.parse_args();result=m.verify(a.historical_view)
print(json.dumps({'status':'PASS_CONTROLLER_PAIR_READ_ONLY_PREFLIGHT','project_seed_modules':len(result['source_declared_project_seed_modules']),'scope':'No Lean; source-declared closure and explicitly contextual endpoint parent.'},sort_keys=True))
