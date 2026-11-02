#!/usr/bin/env python3
"""Check exact report validation against retained successful author logs; no Lean."""
import importlib.util,json,re
from pathlib import Path
p=Path(__file__).resolve().parent;spec=importlib.util.spec_from_file_location('replay',p/'replay.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
base=p.parent;scan=json.loads((base/'compact44-graph-support-carry-closure-plan/scan.json').read_bytes());logs=base/'compact44-fixed-graph-support-carry-prototype/observations'
for row in scan['source_order']:
 name=row['module'];short=name.split('.')[-1];file=logs/('graph-support-attempt01.log' if short=='FixedGraphSupportCarry' else short+'.log');text=file.read_text();assert not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text);m.validate_reports(name,text,row['axiom_reports']);print(short,'retained-report PASS')
 report=row['axiom_reports'][0];small=report=='CleanGeometry.finite_disjoint';old='propext, Quot.sound' if small else 'propext, Classical.choice, Quot.sound';new='propext, Classical.choice, Quot.sound' if small else 'propext, Quot.sound';before="'"+report+"' depends on axioms: ["+old+"]";after="'"+report+"' depends on axioms: ["+new+"]";assert text.count(before)==1
 try:m.validate_reports(name,text.replace(before,after),row['axiom_reports'])
 except ValueError as e:assert 'axiom reports' in str(e)
 else:raise AssertionError(('accepted axiom mutation',report))
 print(report,'mutation-rejected PASS')
