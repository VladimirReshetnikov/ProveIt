#!/usr/bin/env python3
"""Bounded source, external-payload and display-identity audit; no Lean."""
import gzip, hashlib, json, sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):
    raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
def sha(b): return hashlib.sha256(b).hexdigest()
def get(path,expected):
    data=(D/path).read_bytes()
    assert sha(data)==expected,path
    return data
pins={
 'CURRENT_EQUATION.json':'61c6b9255da268b62c306bc0c7eb40b0f5f66b9a74b54086207d8af8c5b98529',
 'equation.tex':'94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635',
 'equation.pdf':'23a52933980352f83a19c21a0d6f349594be5f85edc85a462e25ffc83c7fd5d6',
 'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean':'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea',
 'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean':'0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414',
 'Lean/DiophantineConsistency/Compact44/CompactFourPortByteAssembly2.lean':'3f863dde2c2c5bc3b5dd9789d2e2f5ae70c5856482979b577a4e405f6d7c019e',
 'Lean/DiophantineConsistency/Compact44/CompactBytePortsModelIff.lean':'6a6a15e046bf82817c28e0df884b24f52c0741e24d92149e485fe33836db042d',
 'research/ordinary14-natural86-recipe-port-bridge-draft/Natural86RecipePorts.lean':'0f7011901bdbe9167e10370f3d16c844c5c123146952be5f6a8d385d9b0c4fec',
 'research/ordinary14-natural-forced82-ipra-draft/Natural82Endpoint.lean':'2985f570497227742b56097bbbc184563ae7aa136b8da89e6e201db141a8e13b',
 'research/ordinary14-natural-cancel86-ipra-draft/Natural86Endpoint.lean':'f3755518938e8d3bf4bcb1d33e2dbbfcdc6f2458a414921b1d03ac244503f47c',
 'research/ordinary14-root74-natural-cancel86/candidate.json':'0211a1bcac635af617090facdc3b7f98d18ad94579027df840532d87ae5a5170',
 'research/ordinary14-root74-natural-forced82/candidate.json':'1532ea5ec5f8dee349353044b9618a2e8a633f618e6f7ef5f1d19630b53b6c8a',
 'con-zfc-diophantine-forms/72-congruence-sextic/positive13/ACTIVE_BINDING.json':'6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf',
 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json':'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01',
}
data={name:get(name,h) for name,h in pins.items()}
text=lambda name:data[name].decode('utf-8')
cur=json.loads(data['CURRENT_EQUATION.json'])
assert cur['sha256']['equation.tex']==pins['equation.tex'] and cur['sha256']['equation.pdf']==pins['equation.pdf']
assert (cur['unknowns'],cur['live_binary_operations'],cur['exact_degree'],cur['domain'])==(14,65,150,'strictly positive integers')
tex=text('equation.tex')
assert all(s in tex for s in [r'\rho=2^{47}',r'B=\rho^{2011}',r'\beta=B-1',r'PQUWZ-\Delta=0'])
fixed=text('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean')
ports=text('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean')
assembly=text('Lean/DiophantineConsistency/Compact44/CompactFourPortByteAssembly2.lean')
bytep=text('Lean/DiophantineConsistency/Compact44/CompactBytePortsModelIff.lean')
bridge=text('research/ordinary14-natural86-recipe-port-bridge-draft/Natural86RecipePorts.lean')
assert 'def betaNat : ℕ := 2^(67*8807)-1' in fixed
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports
for s in ['def bytePorts : Fin 4 → List ℕ','Nat.ofDigits 256 (bytePorts j)','theorem decode_ports',
          'RetainedBetaBytes.betaBytes','CompactKernelByteRecipe.bytes','CompactLowByteRecipeData.bytes',
          'CompactShiftedHighByteWindow.bytes']:
    assert s in assembly,s
assert 'def byteP : Fin 4 → ℤ' in bytep and 'theorem byteP_eq : byteP = p' in bytep
assert '(P86NaturalCancel.graph CompactBytePortsModelIff.byteP).output' in bridge and 'rw [CompactBytePortsModelIff.byteP_eq]' in bridge
for path,graph in [('research/ordinary14-natural-forced82-ipra-draft/Natural82Endpoint.lean','P82NaturalForced'),
                   ('research/ordinary14-natural-cancel86-ipra-draft/Natural86Endpoint.lean','P86NaturalCancel')]:
    assert '('+graph+'.graph CompactSymbolicModelIff.p).output' in text(path)
root='con-zfc-diophantine-forms/72-congruence-sextic/positive13/'
p72=json.loads(data[root+'ACTIVE_BINDING.json'])
p115=json.loads(data['con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json'])
observed={}
for name,meta in p72['ports'].items():
    assert meta['encoding']=='gzip of minimal unsigned little-endian bytes'
    other=p115['ports'][name]
    assert all(meta[k]==other[k] for k in ['raw_bytes','bits','sha256_raw','sha256_gzip'])
    compressed=(D/root/meta['path']).read_bytes()
    raw=gzip.decompress(compressed)
    assert sha(compressed)==meta['sha256_gzip'] and sha(raw)==meta['sha256_raw']
    assert len(raw)==meta['raw_bytes'] and int.from_bytes(raw,'little').bit_length()==meta['bits']
    assert raw[-1] != 0
    if name=='beta':
        compact_beta=int.from_bytes(raw,'little')
        assert compact_beta==(1<<(67*8807))-1
        assert raw==bytes([255])*73758+bytes([31])
    observed[name]={'raw_bytes':len(raw),'bits':meta['bits'],'sha256_raw':sha(raw),'sha256_gzip':sha(compressed)}
assert set(observed)=={'beta','K0','MC','MF'}
assert 'Already shifted' in p72['MF_convention']
assert (1<<(47*2011))-1 != compact_beta
candidates={}
for name,path,count in [('natural82','research/ordinary14-root74-natural-forced82/candidate.json',82),
                        ('natural86','research/ordinary14-root74-natural-cancel86/candidate.json',86)]:
    c=json.loads(data[path])
    assert c['operations']==len(c['source'])==count and len(c['witnesses'])==14
    assert c['domain']=='nonnegative integers' and c['fixed_numerals']==['beta','K0','MC','MF']
    candidates[name]={'inputs':14,'domain':c['domain'],'operations':count,'json_sha256':sha(data[path])}
print(json.dumps({'scope':'bounded source-text and external-byte snapshot; no Lean elaboration, file theorem, PDF interpretation or equivalence proof',
 'display':{'tex_sha256':pins['equation.tex'],'pdf_sha256':pins['equation.pdf'],'domain':cur['domain'],
            'variables':14,'operations':65,'degree':150,'printed_beta_exponent':47*2011},
 'compact':{'source_beta_exponent':67*8807,'payload_encoding':'minimal unsigned little-endian, gzip',
            'ports':observed,'MF_is_already_shifted':True},
 'candidate_graphs':candidates,'source_pins':len(pins)},sort_keys=True,indent=2))
