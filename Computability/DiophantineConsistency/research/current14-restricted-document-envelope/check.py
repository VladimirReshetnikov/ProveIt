from pathlib import Path
from hashlib import sha256
import importlib.util, json, re, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current14-restricted-document-envelope')
for p,h in json.loads((D/'pins.json').read_text()).items():
    assert sha256(Path(p).read_bytes()).hexdigest()==h,p
sys.path.insert(0,str(D))
import envelope as impl
import specification as spec
tex=Path('equation.tex').read_text()
fs=spec.DATA['fragments']
pattern=''.join(re.escape(f)+(r'(.*?)' if i<len(fs)-1 else '') for i,f in enumerate(fs))
def independent(document):
    m=re.fullmatch(pattern,document,re.S)
    return m.groups() if m and spec.accepted(document,m.groups()) else None
actual=impl.extract(tex); other=independent(tex)
assert actual is not None and other is not None
assert tuple(actual.values())==other
assert ''.join(f+(other[i] if i<len(other) else '') for i,f in enumerate(fs))==tex

def replace_once(s,a,b):
    assert s.count(a)==1,a
    return s.replace(a,b,1)
invalid={
 'prefix_redefinition':r'\renewcommand{\Delta}{X}'+'\n'+tex,
 'body_redefinition':replace_once(tex,r'b=\beta J',r'b=\renewcommand{\Delta}{X}\beta J'),
 'body_catcode':replace_once(tex,r'b=\beta J',r'b=\catcode`x=0\beta J'),
 'body_hidden_slash':replace_once(tex,r'b=\beta J',r'b=^^5crenewcommand\beta J'),
 'body_comment':replace_once(tex,r'b=\beta J',r'b=%\beta J'),
 'recipe_input':replace_once(tex,r'\rho=2^{47}',r'\rho=\input{evil}2^{47}'),
 'unapproved_environment':replace_once(tex,r'\begin{align*}',r'\begin{filecontents}'),
 'spacing_target':replace_once(tex,r'\setlength{\arraycolsep}{1.4pt}',r'\setlength{\sum}{1.4pt}'),
 'bad_seed_character':replace_once(tex,'128892604103595617','12889260410359561A'),
 'wrapper_tamper':replace_once(tex,'The only unknowns are','Unknowns:'),
}
for name,doc in invalid.items():
    assert impl.extract(doc) is None,name
    assert independent(doc) is None,name
changed_math=replace_once(tex,'q=b+1','q=b+2')
changed_seed=replace_once(tex,'128892604103595617','228892604103595617')
for name,doc,key in [('math',changed_math,'abbreviations'),('seed',changed_seed,'decimal_seed')]:
    got=impl.extract(doc); alt=independent(doc)
    assert got is not None and alt==tuple(got.values()),name
    assert got[key]!=actual[key],name
    assert all(got[k]==actual[k] for k in got if k!=key),name
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'original_tex_sha256':sha256(tex.encode()).hexdigest(),'source_hole_lengths':{k:len(v) for k,v in actual.items()},'independent_relation_accepts':True,'invalid_controls_rejected':sorted(invalid),'changed_math_and_seed_preserved':True,'parsed_formula_or_recipes':False,'lean_executed':False},sort_keys=True,indent=2))
