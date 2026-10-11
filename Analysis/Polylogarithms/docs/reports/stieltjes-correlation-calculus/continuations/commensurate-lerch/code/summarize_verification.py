#!/usr/bin/env python3
"""Combine the three completed verification records without changing them."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
parts=[json.loads((ROOT/'verification'/f'{p}-results.json').read_text()) for p in ('exact','numeric','extra')]
if not all(p['passed'] for p in parts):raise SystemExit('A verification run did not pass')
counts={k:sum(p['counts'][k] for p in parts) for k in ('exact','numerical','negative_control')}
errors=[(float(r['normalized_error']),r['name']) for p in parts for r in p['records'] if r['kind']=='numerical']
out={'counts':counts,'all_completed_runs_passed':True,'largest_normalized_error':max(errors)[0],
     'largest_error_test':max(errors)[1], 'proof_status':'Analytic proofs supplied; diagnostics are not interval or proof-assistant certificates.',
     'runs':[{'part':p['part'],'elapsed_seconds':p['elapsed_seconds'],'working_decimal_digits':p['working_decimal_digits']} for p in parts]}
(ROOT/'verification'/'summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
