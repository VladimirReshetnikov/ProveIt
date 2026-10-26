#!/usr/bin/env python3
"""Verify exact proof-only replacements, hashes, headers, counts, and patch application."""
import argparse,hashlib,json,subprocess
from pathlib import Path
BUNDLE=Path(__file__).resolve().parents[1]
PIN='29936089835c0c55cca81edc86b4fb0c70ce34d5'
p=argparse.ArgumentParser()
p.add_argument('--repo',type=Path)
a=p.parse_args()
records=json.loads((BUNDLE/'evidence/measurements.json').read_text())
summary=[]
for module in dict.fromkeys(r['module'] for r in records):
 rs=[r for r in records if r['module']==module]
 before=(BUNDLE/'baseline/DiophantineConsistency'/f'{module}.lean').read_text()
 after=(BUNDLE/'proposed/DiophantineConsistency'/f'{module}.lean').read_text()
 assert hashlib.sha256(before.encode()).hexdigest()==rs[0]['baseline_sha256']
 assert hashlib.sha256(after.encode()).hexdigest()==rs[0]['proposed_sha256']
 expected=before
 for r in rs:
  assert r['old_declaration'].split(':=',1)[0]==r['new_declaration'].split(':=',1)[0],r['theorem']
  assert expected.count(r['old_declaration'])==1,r['theorem']
  expected=expected.replace(r['old_declaration'],r['new_declaration'])
 if module=='PolynomialRangeBounds':
  expected=expected.replace('import DiophantineConsistency.SelectiveCoefficientBounds\n','import DiophantineConsistency.SelectiveCoefficientBounds\nimport Mathlib.Algebra.Ring.GeomSum\n',1)
 assert expected==after,f'Unexpected non-proof change: {module}'
 old,new=len(before.splitlines()),len(after.splitlines())
 assert (old,new)==(rs[0]['old_module_lines'],rs[0]['new_module_lines'])
 summary.append({'module':module,'before':old,'after':new,'removed':old-new})
 if a.repo:
  current=a.repo/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'/f'{module}.lean'
  assert current.read_text()==before,f'Repository source differs: {module}'
if a.repo:
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=a.repo,text=True).strip()
 assert head==PIN,f'Expected {PIN}, got {head}'
 subprocess.run(['git','apply','--check',str(BUNDLE/'patches/all-four.patch')],cwd=a.repo,check=True)
print(json.dumps({'pin':PIN,'public_headers_preserved':True,'only_listed_proofs_and_one_import_changed':True,'modules':summary,'total_removed':sum(r['removed'] for r in summary)},indent=2))
