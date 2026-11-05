#!/usr/bin/env python3
"""Construct a sheared auxiliary-coordinate candidate; no zero bridge claimed."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];parent=D/'research/current2011-ordinary71-60-candidate/polynomial.json';raw=parent.read_bytes();h=hashlib.sha256(raw).hexdigest()
if h!='3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27':raise RuntimeError('parent drift')
g=json.loads(raw);rows=g['source'];assert rows[54]==['Aaux','*','Delta','f2m1'] and rows[55:60]==[['V2','*','V','V'],['y2','*','y','y'],['aux_gap','-','V2','y2'],['aux_term','*','Aaux','aux_gap'],['Na','+','aux_term','y2']]
tail=[['y_old','+','V','y'],['y_old2','*','y_old','y_old'],['sum_yV','+','y_old','V'],['shear_prod','*','y','sum_yV'],['shear_aux','*','Aaux','shear_prod'],['Na','-','y_old2','shear_aux']]
out={'schema':'literal_integer_arithmetic_dag_v1','name':'current2011_sheared72_degree46_candidate','witness_domain':'strictly positive integers','witnesses':g['witnesses'],'fixed_numerals':g['fixed_numerals'],'coefficient_binding':g['coefficient_binding'],'source':rows[:55]+tail+rows[60:],'output':'polynomial','operations':72,'status':'candidate: shear zero-equivalence and iPRA transfer unchecked','parent_graph_sha256':h,'coordinate_map':'parent y = candidate y + V'}
target=P/'polynomial.json'
if target.exists():raise SystemExit('refusing overwrite')
target.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
