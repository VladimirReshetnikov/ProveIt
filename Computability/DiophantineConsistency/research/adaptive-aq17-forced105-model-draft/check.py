#!/usr/bin/env python3
"""Read-only graph and source checks; never invoke Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/adaptive-aq17-forced105-model-draft/AQ17Forced105Arithmetic.lean.src': 'b3057437cfb476170b28114283783bb0bd392a28f1de1ba4a39b6bf264b5e330', 'research/adaptive-aq17-forced105-model-draft/AQ17Forced105ConditionalTransfer.lean.src': 'd2a5fdb990c7de8008f7f4fbebcbbfcd4a91e43342a436d3aef4be8fd2341473', 'research/adaptive-aq17-forced105-model-draft/AQ17Forced105Literal.lean.src': 'ca9548bcdc73ae480fafe801ad249e45a447f615b0d9bca8edda0c2b74376958', 'research/adaptive-aq17-forced105-model-draft/AQ17Forced105ResidualZeros.lean.src': '767a0adb800e688506f36c2ab4cd5d55deaf05b4c2716fdb3682e204da578021', 'research/adaptive-aq17-forced105-model-draft/AQ17Forced105Residuals.lean.src': 'd9b5cce48d8f89e6e9ec9823f10ebc4ecc23f5c68ba46218c58ef5da15eeb88b', 'research/adaptive-aq17-forced105-model-draft/generate.py': '70dd91773fdf65c94271cd968fe7877fe34998244fad9694f467de0f3e394f47', 'research/adaptive-aq17-forced105-model-draft/generated.json': 'c3819a6e0065146e443c0265daf719d812eb84c736ae484a1d1fd2e6054a1b97', 'research/adaptive-aq17-factored94-model-draft/AQ17Factored94ConditionalTransfer.lean.src': '37d82d6ffc27958025a2752f2c7171b66b8318a801cd314dab74c2a279458d66', 'research/adaptive-aq17-factored94-model-draft/AQ17Factored94Literal.lean.src': 'd419db2a442456bb31c135b3270ab3c19916e04c79f996d02727b36f399333e7', 'research/adaptive-aq17-factored94-model-draft/AQ17Factored94ResidualZeros.lean.src': '21ee415b10988e4cc9dac54e21b15c72a53de0e53caec7d46db032567403036c', 'research/adaptive-aq17-factored94-model-draft/AQ17Factored94Residuals.lean.src': '317e919190e12bafd6bd641338ed154bb2ee201fc3f1c8fe71f9ed645d9418e3', 'research/adaptive-aq17-factored94-model-draft/check.py': 'a0dbc08e46f7212ff59ecaee8768b61fbe7bde6a86e559645d425e328dace58f', 'research/adaptive-aq17-factored94-model-draft/receipt.json': 'a21c9d545217d4f3a84a60aebb0bb0b81e1e567e13b35be9b2e18802dfd8e559', 'research/adaptive-aq17-natural-forced105/candidate.json': 'ff131760c176ebd56a593aff49523daf384c03322e2ddaae07f65f8f63bb7bac', 'research/adaptive-aq17-natural-forced105/check.py': '663eac086d19c56af6615b5e92fcdfbc1713bfdbfdc013722c3894be2a647561', 'research/adaptive-aq17-natural-forced105/receipt.json': '322913d757b9cac60fb64b7c446026e0922c2d6f782456b8fe5de1f74fecec84', 'research/adaptive-aq17-natural-forced104/candidate.json': '1a5f4c54fc5ad2768c676eea1bf875cda7917224e3c4bceebc3d852827fcb55a'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet,check,receipt in [('adaptive-aq17-forced105-model-draft','generate.py','generated.json'),('adaptive-aq17-factored94-model-draft','check.py','receipt.json'),('adaptive-aq17-natural-forced105','check.py','receipt.json')]:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/check)],cwd=D)==(p/receipt).read_bytes(),packet
sources={x.name:x.read_text() for x in P.glob('*.lean.src')}; assert len(sources)==5
for n,s in sources.items(): assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s),n
r=sources['AQ17Forced105Residuals.lean.src'];
assert ': Fin 8 → Expr (Fin 17)' in r and len(re.findall(r'^  !\[([^\n]+)\]$',r,re.M)[0].split(','))==8
c=sources['AQ17Forced105ConditionalTransfer.lean.src'];a=sources['AQ17Forced105Arithmetic.lean.src']
for x in ['ZeroEquivalence','SixForced','ForcingCutExtraction','sixForced_of_cut','h22','h20','h17']:
 assert x in c,x
for x in ['positive_of_square_one_add','ordinate_pos','y_pos_of_zero_product','time_pos','f_pos','j_pos_of_root_branch','((p 1 : ℤ) : DiffRing V)=ι k']:
 assert x in a,x
j=json.loads((D/'research/adaptive-aq17-natural-forced105/candidate.json').read_text())
assert j['operations']==105 and j['forced_unshifted']==['T','f','firstQuotient','mainQuotient','vValueVariable','y']
assert [j['witnesses'][i] for i in (3,5,11,14,15,16)]==['n_f','n_T','n_y','n_firstQuotient','n_mainQuotient','n_vValueVariable']
assert all(f'i={i}' in c for i in (3,5,11,14,15,16))
print(json.dumps({'scope':'bounded source and external graph checks, no Lean','pinned_files':len(pins),'source_files':len(sources),'residual_arity':8,'forced_coordinates':[3,5,11,14,15,16],'graph_identity_and_cut_explicit':True,'optional_J_branch_explicit':True,'source_sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in sorted(sources.items())}},sort_keys=True,indent=2))
