from pathlib import Path
from hashlib import sha256
import importlib.util,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current14-envelope-checker-integration')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
spec=importlib.util.spec_from_file_location('integration',D/'integration.py'); I=importlib.util.module_from_spec(spec);spec.loader.exec_module(I)
tex=Path('equation.tex').read_text()
original_text,original_bytes=Path.read_text,Path.read_bytes
result=I.evaluate(tex)
assert I.reconstruct(result['holes'])==tex
assert result['line_count']==23
expected=json.loads(Path('research/current14-printed-port-recipe-semantic-check/receipt.json').read_text())
assert result['recipe']==expected
assert Path.read_text is original_text and Path.read_bytes is original_bytes

def change(a,b):
    assert tex.count(a)==1,a
    return tex.replace(a,b,1)
changed=change('q=b+1','q=b+2')
try:I.evaluate(changed)
except ValueError as e:assert str(e)=='arithmetic does not match staged quote'
else:raise AssertionError('changed arithmetic accepted')
assert I.envelope.extract(changed) is not None
rejected=[]
for name,a,b in [('recipe','G_{951}', 'G_{950}'),('seed','128892604103595617','228892604103595617')]:
    doc=change(a,b);assert I.envelope.extract(doc) is not None
    try:I.evaluate(doc)
    except AssertionError:rejected.append(name)
    else:raise AssertionError(name+' did not fail the pinned recipe checker')
    assert Path.read_text is original_text and Path.read_bytes is original_bytes
macro=change(r'b=\beta J',r'b=\renewcommand{\Delta}{X}\beta J')
try:I.evaluate(macro)
except ValueError as e:assert str(e)=='envelope rejected'
else:raise AssertionError('macro injection accepted')
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'source_sha256':sha256(tex.encode()).hexdigest(),'actual_regions_forwarded':list(result['holes']),'prefix_line_count':result['line_count'],'existing_recipe_receipt_reproduced':True,'math_mutation_rejected_by_quote_comparison':True,'recipe_and_seed_mutations_rejected_by_original_pin':rejected,'macro_injection_rejected_by_envelope':True,'general_recipe_parser':False,'formal_tex_pdf_semantics':False,'lean_executed':False},sort_keys=True,indent=2))
