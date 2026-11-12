#!/usr/bin/env python3
"""Independent bounded physical-binding source/byte review; does not run Lean."""
from pathlib import Path
import hashlib, json, re, sys, zlib
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D = Path(__file__).resolve().parents[2]
def read(path): return (D / path).read_bytes()
def sha(data): return hashlib.sha256(data).hexdigest()
A = 'research/ordinary14-natural82-86-physical-binding-audit/'
assert sha(read(A+'check.py')) == 'def5c32d8bb3dd34fd81d4c47d29d8f6332eef9390d3d65e537238a05297f837'
assert sha(read(A+'result.json')) == '432e4f2f968a5381c36d8546afb508878a8aff455fec953b65fdd7d1b02f9158'
claim = json.loads(read(A+'result.json'))
# Extract the exponents separately from actual source literals; metadata and
# byte hashes identify snapshots, but do not determine rendered semantics.
tex = read('equation.tex').decode()
meta = json.loads(read('CURRENT_EQUATION.json'))
assert sha(read('equation.tex')) == meta['sha256']['equation.tex']
assert sha(read('equation.pdf')) == meta['sha256']['equation.pdf']
assert (meta['arithmetic_template'],meta['domain'],meta['unknowns'],meta['live_binary_operations'],meta['exact_degree']) == ('Carrier65','strictly positive integers',14,65,150)
t = re.search(r'\\rho=2\^\{(\d+)\},\\quad B=\\rho\^\{(\d+)\},\\quad\\beta=B-1', tex)
assert t
page_n = int(t[1]) * int(t[2])
assert page_n == 94517
base = 'Lean/DiophantineConsistency/Compact44/'
fixed = read(base+'CompactFixedBeta.lean').decode()
b = re.search(r'def betaNat : ℕ := 2\^\((\d+)\*(\d+)\)-1', fixed)
assert b
compact_n = int(b[1]) * int(b[2])
assert compact_n == 590069 and compact_n > page_n
assert (1 << compact_n)-1 != (1 << page_n)-1
# Verify exact mathematical forms of the existing Lean list/tuple declarations.
ports = read(base+'CompactSymbolicPorts.lean').decode()
model = read(base+'CompactSymbolicModelIff.lean').decode()
assembly = read(base+'CompactFourPortByteAssembly2.lean').decode()
byte = read(base+'CompactBytePortsModelIff.lean').decode()
adapter = read('research/ordinary14-natural86-recipe-port-bridge-draft/Natural86RecipePorts.lean').decode()
assert '![β,K,L,β+H]' in ports
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in model
for token in ('def bytePorts : Fin 4 → List ℕ', 'Nat.ofDigits 256 (bytePorts j)', 'theorem decode_ports',
              'RetainedBetaBytes.betaBytes', 'CompactKernelByteRecipe.bytes', 'CompactLowByteRecipeData.bytes', 'CompactShiftedHighByteWindow.bytes'):
    assert token in assembly
for token in ('def byteP : Fin 4 → ℤ', 'theorem byteP_eq : byteP = p', 'congrFun decode_ports j'):
    assert token in byte
assert '(P86NaturalCancel.graph CompactBytePortsModelIff.byteP).output' in adapter
assert 'rw [CompactBytePortsModelIff.byteP_eq]' in adapter
for name,graph in [('ordinary14-natural-forced82-ipra-draft/Natural82Endpoint.lean','P82NaturalForced'),('ordinary14-natural-cancel86-ipra-draft/Natural86Endpoint.lean','P86NaturalCancel')]:
    assert '('+graph+'.graph CompactSymbolicModelIff.p).output' in read('research/'+name).decode()
# Use zlib's gzip decoder independently on all four bound physical payloads.
root = 'con-zfc-diophantine-forms/72-congruence-sextic/positive13/'
a = json.loads(read(root+'ACTIVE_BINDING.json'))
bb = json.loads(read('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json'))
assert set(a['ports']) == set(bb['ports']) == {'beta','K0','MC','MF'}
assert 'Already shifted' in a['MF_convention']
ports_observed={}
for name in sorted(a['ports']):
    info=a['ports'][name]; other=bb['ports'][name]
    assert info['encoding'] == 'gzip of minimal unsigned little-endian bytes'
    for key in ('sha256_gzip','sha256_raw','raw_bytes','bits'): assert info[key] == other[key]
    packed=read(root+info['path']); raw=zlib.decompress(packed,31)
    assert sha(packed)==info['sha256_gzip'] and sha(raw)==info['sha256_raw']
    assert len(raw)==info['raw_bytes'] and raw[-1] != 0
    n=int.from_bytes(raw,'little'); assert n.bit_length()==info['bits']
    if name=='beta': assert n==(1<<compact_n)-1
    ports_observed[name]={'raw_bytes':len(raw),'bits':n.bit_length(),'sha256_raw':sha(raw)}
assert claim['display']['printed_beta_exponent']==page_n
assert claim['compact']['source_beta_exponent']==compact_n
assert claim['compact']['MF_is_already_shifted']
for name, vals in ports_observed.items():
    assert all(claim['compact']['ports'][name][k] == v for k,v in vals.items())
print(json.dumps({'scope':'independent bounded source/byte observations, no Lean or PDF semantics',
 'page_beta_exponent':page_n,'compact_beta_exponent':compact_n,'betas_unequal':True,
 'carrier65_meta':[14,65,150],'reviewed_payloads':ports_observed,
 'decoded_tuple':'[beta,K,L,beta+H]','gzip_decoder':'zlib wbits=31'},sort_keys=True,indent=2))
