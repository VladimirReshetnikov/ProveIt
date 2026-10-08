import json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
if '--external' not in sys.argv: sys.path.insert(1,str(ROOT/'reference_upstream'))
from closure_reset.driver import replay
count=0
for output in sorted((ROOT/'examples').glob('*.result.json')):
    input_file=output.with_name(output.name.replace('.result.json','.json'))
    pd=json.loads(input_file.read_text())['pd']; result=json.loads(output.read_text())
    assert replay(pd,result,max_objects=100000)
    count+=1
print(json.dumps(dict(examples_replayed=count,all_passed=True,external='--external' in sys.argv)))
