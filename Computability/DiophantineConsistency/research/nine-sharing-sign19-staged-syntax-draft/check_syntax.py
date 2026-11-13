#!/usr/bin/env python3
"""Check every staged expression and the assembled seed against pinned AST."""
import contextlib,hashlib,io,json,runpy,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;research=here.parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
seed=research/'nine-sharing-sign19-degree44-y-candidate/seed.json'
assert sha(seed)=='01bae1f7680ce07eb5c041d5ae6a625ead9e79e1c968472521458475a4eb94f1'
parser_path=research/'nine-sharing-sign19-model-bridge-draft/check_syntax.py'
assert sha(parser_path)=='f51fd8694c423f4f856fbc68ca8d075dfdecb0e7d8e166d292266c06e7cb2db8'
with contextlib.redirect_stdout(io.StringIO()):parser=runpy.run_path(str(parser_path))['parse']
rows=json.loads(seed.read_text())['residuals'];assert len(rows)==10
files=[]
for i,r in enumerate(rows):
 p=here/f'SharingSeed19Row{i:02}.lean';s=p.read_text();prefix=f'def row{i:02} (p : Fin 4 → ℤ) : Expr (Fin 20) :=\n  ';assert s.count(prefix)==1
 line=s.split(prefix,1)[1].split('\n',1)[0];assert parser(line)==r['expr'];assert 'sorry' not in s and 'admit' not in s;files.append(p)
p=here/'SharingSeed19Degree44.lean';s=p.read_text();imports='\n'.join(f'import DiophantineConsistency.SharingSeed19Row{i:02}' for i in range(10));assert s.startswith(imports+'\n');items=', '.join(f'row{i:02} p' for i in range(1,10));assert 'def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 20) := row00 p' in s;assert f'def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 20)) := [{items}]' in s
assert '''def seed (p : Fin 4 → ℤ) : Expr (Fin 20) :=
  firstResidual p * firstResidual p +
    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)''' in s
assert 'def zeroWitness (x : ℤ) (j : Fin 20) : ℤ := if j = 0 then x else 0' in s
files.append(p);p=here/'SharingSign19Squares.lean';assert p.read_bytes()==(research/'nine-sharing-sign19-model-bridge-draft/SharingSign19Squares.lean').read_bytes();files.append(p)
print(json.dumps({'status':'PASS_SOURCE_AST_TRANSCRIPTION_ONLY','rows':10,'files':{p.name:sha(p) for p in files},'scope':'Staged rows match pinned external AST and assembly shape; no Lean compilation or model bridge.'},indent=2,sort_keys=True))
