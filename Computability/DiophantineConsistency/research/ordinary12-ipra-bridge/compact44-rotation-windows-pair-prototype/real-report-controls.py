#!/usr/bin/env python3
"""Check exact report validation against retained successful author logs; no Lean."""
import importlib.util,json,re
from pathlib import Path
p=Path(__file__).resolve().parent;spec=importlib.util.spec_from_file_location('replay',p/'replay.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
base=p.parent;scan=json.loads((base/'compact44-rotation-windows-closure-plan/scan.json').read_bytes());dirs=['compact44-fractional-digits-prototype','compact44-rotation-adjacent-prototype','compact44-wrapped-rotation-prototype','compact44-straddling-rotation-prototype','compact44-rotation-coverage-prototype','compact44-rotation-index-bounds-prototype'];logs=[f for d in dirs for f in sorted((base/d/'observations').glob('*.log'))]
for row in scan['source_order']:
 name=row['module'];expected=row['axiom_reports'];matches=[]
 for file in logs:
  text=file.read_text()
  if re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text):continue
  try:m.validate_reports(name,text,expected)
  except ValueError:continue
  matches.append(file)
 assert matches,('missing exact retained report',name)
 text=matches[0].read_text();report=expected[0];before="'"+report+"' depends on axioms: [propext, Classical.choice, Quot.sound]";after="'"+report+"' depends on axioms: [propext, Quot.sound]";assert text.count(before)==1
 try:m.validate_reports(name,text.replace(before,after),expected)
 except ValueError as e:assert 'axiom reports' in str(e)
 else:raise AssertionError(('accepted axiom mutation',report))
 print(name,'retained-report and mutation PASS',matches[0])
