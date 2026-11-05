#!/usr/bin/env python3
"""Link the externally counted split trees to the unique-namespace endpoint source."""
import json,hashlib,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];A=D/'research/nine-current-seed-count-diagnostic';P=D/'research/nine-current-fresh-endpoint/IPRANineFreshCurrent.lean';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P)=='2a6db17518f909026efe5039e13d151dc690e83458edd0762396c9304d001281'
assert sha(A/'check.py')=='7726f6c6ff671cf20c886f2f81ec73edf5553ef30304cd028d9fe30e28fc19d3' and sha(A/'result.json')=='96fb960586db96e143fddbdaf535b186dcdb773a86e4bdc4a1ce862233f23526'
s=P.read_text();frag='''def renameNatural {σ τ : Type*} (f : σ → τ) : NatExpr σ → NatExpr τ
  | .constant a => .constant a
  | .var i => .var (f i)
  | .add p q => .add (renameNatural f p) (renameNatural f q)
  | .mul p q => .mul (renameNatural f p) (renameNatural f q)''';assert frag in s
for x in ['renameNatural Sum.inr ObjectCurrentEquation2011.naturalExpression.splitNatural.1','renameNatural Sum.inr ObjectCurrentEquation2011.naturalExpression.splitNatural.2','QuarticCompiler.witnessCount left right','QuarticSyntax.expression left right','ExecutableJones.expression seed 0']:assert x in s,x
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],capture_output=True);assert r.returncode==0 and r.stdout==(A/'result.json').read_bytes();d=json.loads(r.stdout);assert (d['left_nodes'],d['right_nodes'],d['quartic_witness_count'])==(8446685,8446685,16893385)
print(json.dumps({'status':'PASS_EXTERNAL_LINK','left_nodes':8446685,'right_nodes':8446685,'quartic_witness_count':16893385,'scope':'Source structural linkage; no Lean numeric count equality, Jones graph or degree theorem.'},indent=2,sort_keys=True))
