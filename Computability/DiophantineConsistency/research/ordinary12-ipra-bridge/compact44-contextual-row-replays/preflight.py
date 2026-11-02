#!/usr/bin/env python3
"""No-Lean contextual-parent preflight for the inverse or exclusion variant."""
import argparse,importlib.util,json,os,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
BASE=Path(__file__).resolve().parents[1];ap=argparse.ArgumentParser();ap.add_argument('--kind',choices=('inverse','exclusion'),required=True);ap.add_argument('--historical-view',type=Path,required=True);a=ap.parse_args()
p=BASE/('compact44-inverse-lookup-prototype' if a.kind=='inverse' else 'compact44-model-noextra-prototype')/'contextual-replay.py';s=importlib.util.spec_from_file_location('contextual_driver',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);m.pins();r=m.audit(a.historical_view)
print(json.dumps({'status':'PASS_CONTEXTUAL_ROW_READ_ONLY_PREFLIGHT','kind':a.kind,'parent_statuses':[x['status'] for x in r] if isinstance(r,list) else [r['status']],'scope':'No Lean; explicit contextual historical row-parent rerun.'},sort_keys=True))
