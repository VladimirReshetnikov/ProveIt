#!/usr/bin/env python3
"""Check exact report validation against retained successful author logs; no Lean."""
import importlib.util,json,re
from pathlib import Path
p=Path(__file__).resolve().parent;spec=importlib.util.spec_from_file_location('replay',p/'replay.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
base=p.parent;scan=json.loads((base/'compact44-indexed-mass-carry-closure-plan/scan.json').read_bytes());logs=base/'compact44-indexed-band-flatten-prototype/observations';fixed=base/'compact44-fixed-graph-indexed-carry-prototype/observations/fixed-graph-attempt02.log'
for row in scan['source_order']:
 name=row['module'];short=name.split('.')[-1]
 if short=='FixedGraphIndexedCarry':file=fixed
 elif short=='CompactTwoBandFlatten':file=logs/'twoband-attempt02.log'
 elif short=='CompactTwoBandCarry':file=logs/'carry-attempt01.log'
 else:file=logs/(short+'.log')
 text=file.read_text();assert not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text);m.validate_reports(name,text,row['axiom_reports']);print(short,'retained-report PASS')
 if short=='CompactSelectorMassBridge':
  for report,old,new in [('CompactSelectorMassBridge.ofFn_get_cast','propext, Quot.sound','propext, Classical.choice, Quot.sound'),('CompactSelectorMassBridge.rows_ofFn','propext, Quot.sound','propext, Classical.choice, Quot.sound'),('CompactSelectorMassBridge.copy_fin_mass','propext, Classical.choice, Quot.sound','propext, Quot.sound')]:
   before="'"+report+"' depends on axioms: ["+old+"]";after="'"+report+"' depends on axioms: ["+new+"]";assert text.count(before)==1
   try:m.validate_reports(name,text.replace(before,after),row['axiom_reports'])
   except ValueError as e:assert 'axiom reports' in str(e)
   else:raise AssertionError(('accepted axiom mutation',report))
   print(report,'mutation-rejected PASS')
