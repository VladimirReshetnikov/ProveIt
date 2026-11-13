#!/usr/bin/env python3
"""Check report guard against retained same-overlay author logs; no Lean."""
import hashlib,importlib.util,json,re
from pathlib import Path
p=Path(__file__).resolve().parent;spec=importlib.util.spec_from_file_location('replay',p/'replay.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
survey=json.loads((p/'report-survey.json').read_bytes());scan=json.loads((p.parent/'compact44-fixed-clean-carry-closure-plan/scan.json').read_bytes());assert survey['source_modules']==33 and survey['reports']==54 and survey['source_scan_sha256']==hashlib.sha256((p.parent/'compact44-fixed-clean-carry-closure-plan/scan.json').read_bytes()).hexdigest()
for row,seen in zip(scan['source_order'],survey['rows']):
 assert row['module']==seen['module'] and row['source_sha256']==seen['source_sha256'];file=Path(seen['retained_log']);text=file.read_text();assert hashlib.sha256(file.read_bytes()).hexdigest()==seen['log_sha256'] and not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text);m.validate_reports(row['module'],text,row['axiom_reports']);print(row['module'],'retained-report PASS')
 for report in row['axiom_reports']:
  small=report in m.SMALL_AXIOMS;old='propext, Quot.sound' if small else 'propext, Classical.choice, Quot.sound';new='propext, Classical.choice, Quot.sound' if small else 'propext, Quot.sound';before="'"+report+"' depends on axioms: ["+old+"]";after="'"+report+"' depends on axioms: ["+new+"]";assert text.count(before)==1
  try:m.validate_reports(row['module'],text.replace(before,after),row['axiom_reports'])
  except ValueError as e:assert 'axiom reports' in str(e)
  else:raise AssertionError(('accepted axiom mutation',report))
print('all 54 exact retained reports and per-report mutations PASS')
