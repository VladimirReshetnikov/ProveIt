#!/usr/bin/env python3
"""Pin both source-draft interfaces and check full hypothesis transcription."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-eta-zero-p72-index-draft/P72ExactEtaNatural.lean.src':'b02fbec88cc6fbf58651346920fd9626790e623c79bdcb5c2f73f4ff68e88f63',
'research/pell-main-ordinate-parity-model-draft/PellOrdinateParity.lean.src':'bb0e98110be0d3c091c6d00c6b72a60232dfd17cd1d673fdce6cf6617ef189b1'}
def pin(p,h):
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s={p:pin(p,h) for p,h in pins.items()}
p=s['research/ordinary13-eta-zero-p72-index-draft/P72ExactEtaNatural.lean.src']
h=p.index('theorem indices_ordinary');start=p.index('(hq3',h);end=p.index(' :\n    13 ≤ n',start)
hyp=p[start:end]
assert hyp.count('(hc : c = η + Y * k)')==1
hyp=hyp.replace('(hc : c = η + Y * k)','(hc : c = Y * k)')
b=(here/'EtaZeroIndexParity.lean.src').read_bytes();d=b.decode()
h=d.index('theorem eta_zero_contradiction');start=d.index('(hq3',h);end=d.index(' :\n    False',start)
assert d[start:end]==hyp,'one or more index hypotheses changed'
assert 'theorem ordinate_mod_two (n b : V) : ycoord n b % 2 = n % 2' in s['research/pell-main-ordinate-parity-model-draft/PellOrdinateParity.lean.src']
for term in ('P72ExactEtaNaturalDraft.indices_ordinary','PellOrdinateParityModelDraft.ordinate_mod_two','mod_two R','← hny','haux'):assert term in d
assert 'sorry' not in d and '\naxiom ' not in d
print(json.dumps({'provider_sha256':pins,'client_sha256':hashlib.sha256(b).hexdigest(),'all_index_hypotheses_exact_mod_eta_zero':True,'scope':'lexical draft composition only; no Lean elaboration, graph zero maps, provider closure, or iPRA endpoint','lean_elaborated':False},sort_keys=True,indent=2))
