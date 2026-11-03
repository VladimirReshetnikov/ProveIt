#!/usr/bin/env python3
"""Check selected author receipts and direct imported object pins without invoking Lean."""
import ast,json,re,hashlib
from pathlib import Path
D=Path(__file__).resolve().parents[2];R=D/'research'
rows=[('ten-positive-reverse-cross-prototype','ReverseCross','cross-attempt02','TenPositiveReverseCross.cross_zero','4f9440ae58ba151097fcfbb040a519adbff3414577022b821a50e8c4a15eb4d0'),('ten-positive-80-reverse-output-parts-prototype','Direct80ReverseOutputParts','parts-attempt02','TenPositive80ReverseOutputParts.output_zero','a74ef818061432bddc4914aea57c52e3e08e705ffb385ccf4fe6b387ce07b33e')]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for directory,name,attempt,theorem,objhash in rows:
 p=R/directory;obs=p/'observations'/attempt;r=json.loads((obs/'terminal.json').read_text()); source=p/(name+'.lean');runner=p/'run.py'
 assert r['exit']==0 and r['reason'] is None and r['pins']==r['after']
 assert sha(source)==r['pins']['source']==sha(obs/'source.txt') and sha(runner)==r['pins']['runner']
 assert sha(obs/'stdout')==r['stdout_sha256'] and sha(obs/'stderr')==r['stderr_sha256']
 assert sha(Path(r['output_root'])/(name+'.olean'))==r['object_sha256']==objhash
 out=(obs/'stdout').read_text()+(obs/'stderr').read_text()
 assert f"'{theorem}' depends on axioms: [propext, Quot.sound]" in out
 assert not re.search(r'\b(?:error|warning)(?:\([^)]*\))?:|sorryAx',out)
 script=ast.parse(runner.read_text()); assignments=[x for x in script.body if isinstance(x,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='expected_direct' for t in x.targets)]
 assert len(assignments)==1;expected=ast.literal_eval(assignments[0].value)
 imports=[m for line in source.read_text().splitlines() if line.startswith('import ') for m in line[7:].split()]
 assert set(imports)==set(expected)==set(r['pins']['direct_imports'])
 print(name,'source',sha(source),'runner',sha(runner),'object',objhash)
 for module in imports:
  selected=next(Path(x)/(module.replace('.','/')+'.olean') for x in r['lean_path'].split(':') if (Path(x)/(module.replace('.','/')+'.olean')).is_file())
  got=r['pins']['direct_imports'][module];want=expected[module]
  assert str(selected)==got['path']==want['path'] and str(selected.resolve())==got['real_path'] and sha(selected)==got['sha256']==want['sha256']
  print(' ',module,str(selected),sha(selected))
 print('  terminal',sha(obs/'terminal.json'))
print('PASS: current sources, receipt copies, outputs, direct import pins and first selection; no Lean replay')
