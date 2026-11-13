#!/usr/bin/env python3
import pathlib,json,hashlib,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/nine-current-fresh-seed-count-link';Q=D/'reviews/nine-current-seed-count-independent';E=D/'research/nine-current-fresh-endpoint/IPRANineFreshCurrent.lean'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert sha(E)=='2a6db17518f909026efe5039e13d151dc690e83458edd0762396c9304d001281';s=E.read_text()
for x in ['def renameNatural {σ τ : Type*}','| .constant a => .constant a','| .var i => .var (f i)','| .add p q => .add (renameNatural f p) (renameNatural f q)','| .mul p q => .mul (renameNatural f p) (renameNatural f q)','renameNatural Sum.inr ObjectCurrentEquation2011.naturalExpression.splitNatural.1','renameNatural Sum.inr ObjectCurrentEquation2011.naturalExpression.splitNatural.2','QuarticCompiler.witnessCount left right','QuarticSyntax.expression left right','ExecutableJones.expression seed 0']:assert x in s,x
q=subprocess.run([sys.executable,str(Q/'check.py')],capture_output=True);assert q.returncode==0 and not q.stderr and q.stdout==(Q/'result.json').read_bytes();d=json.loads(q.stdout);assert (d['left_nodes'],d['right_nodes'],d['quartic_witness_count'])==(8446685,8446685,16893385)
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],capture_output=True);assert q.returncode==0 and not q.stderr and q.stdout==(P/'result.json').read_bytes()
print(json.dumps({'status':'PASS','left_nodes':8446685,'right_nodes':8446685,'quartic_witness_count':16893385,'scope':'External source linkage only; no Lean count theorem or nine-variable graph/degree.'},indent=2))
