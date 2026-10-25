#!/usr/bin/env python3
"""Freeze a compact summary of a completed normal/optimized isolated replay.

Run only against an actual PASS receipt. A PASS is finite replay, not a proof
of any inherited unbounded semantic theorem.
"""
from pathlib import Path
import argparse,json,hashlib
import reproduce as R
ROOT=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--receipt',required=True,type=Path);a=ap.parse_args()
    r=json.loads(a.receipt.read_text())
    R.need(r['status']=='PASS','replay not passed')
    files=set()
    for mode in ['normal','optimized']:
        R.need(r[mode]['status']=='PASS','missing passed '+mode+' replay')
        files.update(r[mode]['exact_byte_comparisons'])
    code=json.loads((ROOT/'CODE_REVIEW.json').read_text())['files']
    summary={'schema':'round17_frozen_replay_summary_v1','status':'PASS',
      'scope':r['scope'],'python':r['python'],'sympy':r.get('sympy'),
      'receipt_sha256':R.digest(a.receipt.read_bytes()),
      'replay_plan_sha256':R.digest((ROOT/'REPRODUCE_PLAN.json').read_bytes()),
      'code_review_sha256':R.digest((ROOT/'CODE_REVIEW.json').read_bytes()),
      'exact_byte_comparison_sha256':{},'execution_source_sha256':{},
      'modes':{},'negative_controls':r['negative_controls']}
    for rel in sorted(files):
        R.safe(rel);summary['exact_byte_comparison_sha256'][rel]=R.digest((ROOT/rel).read_bytes())
    for row in code:
        R.safe(row['path']);actual=R.digest((ROOT/row['path']).read_bytes())
        R.need(actual==row['sha256'],'reviewed source differs: '+row['path'])
        summary['execution_source_sha256'][row['path']]=actual
    for mode in ['normal','optimized']:
        summary['modes'][mode]={'status':'PASS','commands':len(r[mode]['commands']),
          'exact_byte_comparisons':len(r[mode]['exact_byte_comparisons']),
          'unchanged_coefficient_files':r[mode]['unchanged_coefficient_files']}
    (ROOT/'REPLAY_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({'status':'PASS','comparisons':len(files),'reviewed_source_files':len(code)}))
if __name__=='__main__':main()
