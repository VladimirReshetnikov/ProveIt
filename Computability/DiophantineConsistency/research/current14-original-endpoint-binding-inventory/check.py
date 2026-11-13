from pathlib import Path
from hashlib import sha256
import json, subprocess, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current14-original-endpoint-binding-inventory')
pins=json.loads((D/'pins.json').read_text())
for p,h in pins.items(): assert sha256(Path(p).read_bytes()).hexdigest()==h,p
reviews=['reviews/current14-restricted-tex-extractor-independent','reviews/current14-printed-port-recipe-independent']
for r in reviews:
    actual=subprocess.run([sys.executable,'-I','-S','-B',r+'/check.py'],check=True,stdout=subprocess.PIPE,timeout=25).stdout
    assert actual==Path(r+'/receipt.json').read_bytes(), r
arithmetic=json.loads(Path(reviews[0]+'/pins.json').read_text())
ports=json.loads(Path(reviews[1]+'/pins.json').read_text())
tex=sha256(Path('equation.tex').read_bytes()).hexdigest()
assert arithmetic['equation.tex']==ports['equation.tex']==tex
lp=Path('research/nine-sharing-sign17-lines-current14-endpoint-check/src/DiophantineConsistency/Sign17LinesCurrent14Endpoint.lean').read_text()
for t in ['def linePorts : Fin 4 → ℤ', 'theorem linePorts_eq : linePorts = CurrentWindowCarry2011.ports', 'theorem linePorts_recipes', 'exact Current14LiteralPortsMF.all_ports', 'theorem line_endpoint_translated', 'noZeroAt linePorts 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ']:
    assert t in lp,t
q=Path('research/current14-seed-readable-prefix-staged-check/src/DiophantineConsistency/Current14QuotedPrefixEndpoint.lean').read_text()
for t in ['import DiophantineConsistency.Current14QuotedPrefixQuote','let e ← quotedExpr linePorts','theorem quoteSentence_eq']:
    assert t in q,t
end=Path('research/current14-quoted-translated-endpoint-check/src/DiophantineConsistency/Current14QuotedTranslatedEndpoint.lean').read_text()
for t in ['import DiophantineConsistency.Current14QuotedPrefixEndpoint','theorem quoted_translated_endpoint','standardTheory ⊢ φ 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ','exact line_endpoint_translated']:
    assert t in end,t
terminal={}
for n in ['nine-sharing-sign17-lines-current14-endpoint-terminal-independent','current14-seed-readable-prefix-staged-terminal-independent','current14-quoted-translated-endpoint-terminal-independent']:
    x=json.loads(Path('reviews',n,'result.json').read_text()); assert x['status']=='PASS_TERMINAL_AUDIT',n
    terminal[n]={'status':x['status'],'outer_session':x.get('outer_session')}
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'shared_tex_sha256':tex,'independent_finite_reviews_reproduced':reviews,'source_shape_checks':True,'recorded_terminal_reviews':terminal,'terminal_replays_repeated':False,'lean_executed':False,'formal_tex_pdf_semantics':False,'coherent_current_source_provider_authenticated':False},sort_keys=True,indent=2))
