from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current14-tex-token-boundary-client-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
quote=Path('research/current14-seed-readable-prefix-staged-check/src/DiophantineConsistency/Current14QuotedPrefixQuote.lean').read_text()
core=Path('research/current14-seed-readable-prefix-staged-check/src/DiophantineConsistency/Current14QuotedPrefixCore.lean').read_text()
ep=Path('research/current14-seed-readable-prefix-staged-check/src/DiophantineConsistency/Current14QuotedPrefixEndpoint.lean').read_text()
trans=Path('research/current14-quoted-translated-endpoint-check/src/DiophantineConsistency/Current14QuotedTranslatedEndpoint.lean').read_text()
s=(D/'Current14TexTokenBoundary.lean.src').read_text()
for x in ['def quoted : List (List String)','def quotedExpr (p : Fin 4 → ℤ)','theorem quotedExpr_eq']:assert x in quote
for x in ['def initial (p : Fin 4 → ℤ)','def compile : Env → List (List String) → Option Env','def lookup (name : String)']:assert x in core
for x in ['def quoteSentence : Option (Sentenceᵢ language)','let e ← quotedExpr linePorts','let e := positiveShift e']:assert x in ep
for x in ['theorem quoted_translated_endpoint : ∃ φ, quoteSentence = some φ','(standardTheory ⊢ φ 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ)']:assert x in trans
for x in ['def sentenceFromTokens','compile (initial linePorts) lines','lookup "result" env','theorem sentenceFromTokens_quoted','(hextract : extract bytes = some quoted)','quoted_translated_endpoint','#print axioms']:assert x in s
# Compare the final sentence constructor text exactly to the historical endpoint.
a=ep.split('  let e := positiveShift e',1)[1].split('\ntheorem quoteSentence_eq',1)[0]
b=s.split('  let e := positiveShift e',1)[1].split('\n/-- The fixed normalized quote',1)[0]
assert a.strip()==b.strip()
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'checked_fixed_token_and_endpoint_source_interfaces':True,'exact_sentence_constructor_text':True,'extractor_is_explicit_unproved_parameter':True,'raw_tex_or_pdf_formally_bound':False,'lean_executed':False},sort_keys=True,indent=2))
