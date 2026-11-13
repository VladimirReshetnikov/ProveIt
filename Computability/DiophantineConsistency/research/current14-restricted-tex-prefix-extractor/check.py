from pathlib import Path
from hashlib import sha256
import importlib.util,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current14-restricted-tex-prefix-extractor')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
spec=importlib.util.spec_from_file_location('restricted_equation_extractor',D/'extract.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
tex=Path('equation.tex').read_text();source=Path('research/current14-seed-readable-prefix-staged-check/src/DiophantineConsistency/Current14QuotedPrefixQuote.lean').read_text()
parsed=mod.extract(tex);quote=mod.lean_quote(source)
assert len(parsed)==23 and parsed==quote
variables=r'J,F,\alpha,z,f,i,T,s,w,n,\eta,\zeta,y,\gamma\in\mathbb Z_{>0}'
assert variables in tex
core=Path('research/current14-seed-readable-prefix-staged-check/src/DiophantineConsistency/Current14QuotedPrefixCore.lean').read_text()
assert re.findall(r'\("([A-Za-z]+)", \.var (\d+)\)',core)==list(zip(mod.VARIABLES,map(str,range(14))))
assert re.findall(r'\("(beta|K|mu|omega)", \.constant \(p (\d)\)\)',core)==list(zip(mod.PORTS,map(str,range(4))))
# Every variant either rejects or disagrees with the fixed normalized quote.
mutations=[
 ('changed_plus',tex.replace('q=b+1','q=b-1',1)),
 ('changed_subtraction',tex.replace('C=q-F-\\alpha','C=q-(F-\\alpha)',1)),
 ('changed_square',tex.replace('P=\\tau^2','P=\\tau^3',1)),
 ('unrecognized_macro',tex.replace('X=wq','X=w\\unknown q',1)),
 ('unknown_variable',tex.replace('X=wq','X=wMq',1)),
 ('mismatched_parenthesis',tex.replace('X=wq','X=(wq',1)),
 ('duplicate_declaration',tex.replace('X=wq','C=wq',1)),
 ('trailing_box_token',tex.replace('PQUWZ-\\Delta=0.','PQUWZ-\\Delta J=0.',1)),
 ('changed_zero',tex.replace('PQUWZ-\\Delta=0.','PQUWZ-\\Delta=1.',1)),
]
observed={}
for name,changed in mutations:
 assert changed!=tex,name
 try:
  result=mod.extract(changed)
  assert result!=quote,name
  observed[name]='different tokens'
 except mod.ParseError:observed[name]='rejected'
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'actual_tex_derived_lines':len(parsed),'equal_to_historical_prefix_tokens':True,'ordered_positive_variable_source_string_checked':True,'mutations':observed,'port_recipe_parsed':False,'tex_semantics_or_pdf_formally_checked':False,'lean_executed':False},sort_keys=True,indent=2))
