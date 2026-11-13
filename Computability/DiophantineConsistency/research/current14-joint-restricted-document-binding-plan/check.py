from pathlib import Path
from hashlib import sha256
import json, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current14-joint-restricted-document-binding-plan')
for p,h in json.loads((D/'pins.json').read_text()).items():
    assert sha256(Path(p).read_bytes()).hexdigest()==h,p
tex=Path('equation.tex').read_text()
for fragment in [r'\let\bigsum\sum\renewcommand{\sum}{\bigsum\nolimits}',r'\newcommand{\fl}[1]{\left\lfloor#1\right\rfloor}',r'\newcommand{\rg}[2]{\{#1,\ldots,#2\}}','The only unknowns are','The single equation is',r'\textbf{The four fixed integers.}',r'\textbf{The 942 indexed fixed tiles.}',r'\textbf{A closed decoder for the 430 actions.}',r'\textbf{The integer $\mathcal A$ in base 10.}']:
    assert tex.count(fragment)==1,fragment
quote=Path('research/current14-seed-readable-prefix-staged-check/src/DiophantineConsistency/Current14QuotedPrefixQuote.lean').read_text()
for fragment in ['def quoted : List (List String)', 'theorem quotedExpr_eq (p : Fin 4 → ℤ)', 'quotedExpr p = some (displayedExpr p)']:
    assert fragment in quote, fragment
recipe=Path('research/nine-sharing-sign17-literal-ports-replay-check/src/DiophantineConsistency/Sign17LiteralPorts.lean').read_text()
for fragment in ['def beta : ℤ', 'def mu : ℤ', 'def omega : ℤ', 'def K : ℚ', 'theorem all_ports', '(CurrentWindowCarry2011.ports 1 : ℚ) = K']:
    assert fragment in recipe, fragment
line=Path('research/nine-sharing-sign17-lines-current14-endpoint-check/src/DiophantineConsistency/Sign17LinesCurrent14Endpoint.lean').read_text()
for fragment in ['theorem linePorts_recipes', '(linePorts 1 : ℚ) = Current14LiteralPortsMF.K', 'theorem line_endpoint_translated']:
    assert fragment in line,fragment
h=Path('Lean/DiophantineConsistency/HACurrentEquation2011.lean').read_text()
assert 'theorem ha_current_iff_consistency' in h
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'exact_page_macro_and_section_shapes_checked':True,'uniform_quote_port_and_rational_recipe_interfaces_found':True,'ha_source_endpoint_found':True,'parser_implemented_here':False,'lean_executed':False,'proof_provider_audited':False},sort_keys=True,indent=2))
