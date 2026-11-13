#!/usr/bin/env python3
"""Bind every selected native-bit paired source to its independently audited author row."""
import hashlib,json
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1];RUN=Path('/tmp/ipra-selected-native-bit-historical-paired-run-01');AUTHOR=BASE/'reviews/ipra-selected-native-bit-guarded-author';AUDIT=BASE/'reviews/ipra-selected-native-bit-guarded-author-independent-audit'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
manifest=J(RUN/'snapshot/manifest.json');state=J(AUTHOR/'state.json');prior=J(AUDIT/'receipt.json');terminal=J(AUDIT/'terminal-observation.json')
assert H(AUDIT/'receipt.json')=='e47a76773c98a19ffdf90165ffda5b2f338c9b03bb31f92cc7aa8403656c8516'
assert prior['status']=='PASS_INDEPENDENT_SELECTED_NATIVE_BIT_AUTHOR_ARTIFACT_AUDIT' and terminal['observed_exit_code']==0 and terminal['receipt_sha256']==H(AUDIT/'receipt.json')
assert prior['trial_state_sha256']==H(AUTHOR/'state.json')
names=[r['module'] for r in state['rows']];assert len(names)==11 and names==manifest['order'][1210:]
sources=[]
for row in state['rows']:
 name=row['module'];source=RUN/'snapshot'/manifest['sources'][name]['snapshot_path']
 assert H(source)==row['source_sha256']==manifest['sources'][name]['sha256'];sources.append(source)
bit=sources[-1].read_text();checker=sources[-2].read_text();matrix=sources[-3].read_text()
assert 'theorem selected_checker_endpoints : ∃ c : Code 1,' in checker
assert 'PRA ⊢ PRACharacteristicBit.bitSentence c' in checker
assert 'nativeTheory ⊢ (∼mappedNativeRefutation embedding 🡘 ∼checkerRefutation c)' in checker
assert 'standardTheory ⊢ (∼mappedNativeRefutation embedding 🡘 ∼checkerRefutation c)' in checker
assert 'IPRAStandardSquareSums13.literal_equivalence' in checker and 'IPRAStandardProduct13.literal_equivalence' in checker
assert 'extended nativeTheory ⊢ native (Rew.embSubsts e ▹ oneAtom c)' in matrix
statement=' '.join(bit.split('theorem selected_checker_boolean_endpoints :',1)[1].split(':= by',1)[0].split())
assert statement==('∃ c : Code 1, Primrec (PRAFiniteFunctionCodes.eval c) ∧ nativeTheory ⊢ nativeBitSentence c ∧ standardTheory ⊢ nativeBitSentence c ∧ '
    'standardTheory ⊢ (IPRAExpressionNative.nativeNoZero (AdaptiveEquationSyntax2011.positiveShift (AdaptiveDirectOrdinateSquareSumsLiteral.literal CurrentWindowCarry2011.ports)) 🡘 ∼checkerRefutation c) ∧ '
    'standardTheory ⊢ (IPRAExpressionNative.nativeNoZero AdaptiveDirectOrdinate86Literal.naturalExpression86 🡘 ∼checkerRefutation c)')
assert 'obtain ⟨c, hp, hb, _, _, hs, ht⟩ := selected_checker_endpoints' in bit
files=[Path(__file__),*sources,RUN/'snapshot/manifest.json',AUTHOR/'state.json',AUDIT/'receipt.json',AUDIT/'terminal-observation.json'];before={str(p.resolve()):H(p) for p in files}
assert {str(p.resolve()):H(p) for p in files}==before
result={'status':'PASS_SELECTED_NATIVE_BIT_PAIRED_ENDPOINT_SOURCE_LINK','inputs_sha256':before,'scope':'Finite source link to historical author audit; code existential, native and standard intuitionistic bit theorems, no arbitrary-checker comparison or PDF semantics.'};out=HERE/'endpoint-link-receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result['status'],H(out))
