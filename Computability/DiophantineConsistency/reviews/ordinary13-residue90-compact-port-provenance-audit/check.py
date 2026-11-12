#!/usr/bin/env python3
"""Bounded four-port source, retained payload and display provenance audit; no Lean."""
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b
files={
'draft':('research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src','11ba8e4e01d29b956926a26b04815d5a660b79caabfce7b8cc1ce6d5c85d615a'),
'ports':('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean','0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414'),
'beta':('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean','bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea'),
'kernel':('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernel.lean','9b2b73430cbf4578ef4b4c7d4658c9526b7ebdc423263470df907a16b454ba55'),
'param':('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernelOpaque.lean','8ae9ed11d9e7408e4fd71555569181b0fb785f24f3177facc6c6c997d0d5e615'),
'assembly':('Lean/DiophantineConsistency/Compact44/CompactFourPortByteAssembly2.lean','3f863dde2c2c5bc3b5dd9789d2e2f5ae70c5856482979b577a4e405f6d7c019e'),
'byteiff':('Lean/DiophantineConsistency/Compact44/CompactBytePortsModelIff.lean','6a6a15e046bf82817c28e0df884b24f52c0741e24d92149e485fe33836db042d'),
'betabyte':('Lean/DiophantineConsistency/Compact44/RetainedBetaBytes.lean','25fb9a33c312f1a2a100292e963525bb60f49c44d924b24e0f5f8ea37c5518a7'),
'kbyte':('Lean/DiophantineConsistency/Compact44/CompactKernelByteRecipe.lean','f34ce84437f4baab121140f942189ea0117a781fe3fb67940a1a30a5b88c5e07'),
'lowbyte':('Lean/DiophantineConsistency/Compact44/CompactLowByteAssembly.lean','ad1e7282418407248a85e45c41a63980eaaa16181ebc8280b105d19f08bbd32f'),
'highbyte':('Lean/DiophantineConsistency/Compact44/CompactShiftedHighByteAssembly.lean','0e05ebc1b2e0b09a1be90445cbfbedbe46bab5a66a3dd1982254f56230ce7b36'),
'proj':('Lean/DiophantineConsistency/Compact44/CompactSymbolicPortProjections.lean','afcd2404ad66cd22843ae936d8a70cc64399cce762c8deb7adfe16be6a01516e'),
'symbolic':('Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean','379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46'),
'uncond':('Lean/DiophantineConsistency/Compact44/CompactSymbolicModelUnconditionalIff.lean','ea2dbe86aaebf241d233a1cde5860157da34cf2e20ae943aef42516c659888aa'),
'endpoint':('Lean/DiophantineConsistency/Compact44/IPRAOrdinary13.lean','c6b54e6098062be18966a9fd5891284909bd1454d6d6ee8b0db26e808045a735')}
s={k:pin(*v).decode() for k,v in files.items()}
for k,fragments in {'draft':['def ports (K : ℕ)','CompactSymbolicPorts.ports CompactFixedBeta.betaNat K','CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat','theorem cast_port'], 'ports':['def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]','def lowNat','def highNat'], 'beta':['def betaNat : ℕ := 2^(67*8807)-1','theorem beta_identity'], 'kernel':['def rho : ℕ := 2^67'], 'param':['def paramKernel (r : ℕ)','theorem cast_paramKernel'], 'assembly':['theorem decode_ports','RetainedBetaBytes.decode_betaBytes CompactKernelByteRecipe.decode_bytes','CompactLowByteAssembly.decode_bytes CompactShiftedHighByteAssembly.decode_bytes'], 'byteiff':['theorem byteP_eq : byteP = p','((Nat.ofDigits 256 (bytePorts j) : ℕ) : ℤ)'], 'betabyte':['theorem decode_betaBytes'], 'kbyte':['theorem decode_bytes'], 'lowbyte':['theorem decode_bytes'], 'highbyte':['CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat'], 'proj':['theorem beta (K : ℕ)','theorem kernel (K : ℕ)','theorem low (K : ℕ)','theorem high (K : ℕ)'], 'symbolic':['ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat','(hbeta :','(hK :','(hMC :','(hMF :'], 'uncond':['theorem model_iff','CompactSymbolicPortProjections.kernel (paramKernel rho)'], 'endpoint':['FreeJ13.graph CompactSymbolicModelIff.p','theorem native_equivalence']}.items():
 for f in fragments:assert f in s[k],(k,f)
p72root='con-zfc-diophantine-forms/72-congruence-sextic/positive13/'
p115root='con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/'
p72=json.loads(pin(p72root+'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
p115=json.loads(pin(p115root+'BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
values={}
for name,a in p72['ports'].items():
 b=p115['ports'][name]
 assert all(a[key]==b[key] for key in ['bits','raw_bytes','sha256_raw','sha256_gzip'])
 packed72=pin(p72root+a['path'],a['sha256_gzip']);packed115=pin(p115root+b['file'],b['sha256_gzip'])
 assert packed72==packed115
 raw=gzip.decompress(packed72);assert len(raw)==a['raw_bytes'] and hashlib.sha256(raw).hexdigest()==a['sha256_raw']
 assert gzip.decompress(packed115)==raw
 values[name]=int.from_bytes(raw,'little');assert values[name].bit_length()==a['bits']
assert values['beta']==(1<<(67*8807))-1
assert p72['MF_convention'].startswith('Already shifted') and p115['warning'].startswith('MF is the already shifted')
pin('reviews/ordinary14-natural79-decimal-port-math-independent/check.py','6c1e950d6235617b0d76103a50e30b17b69c6182a5b7fd5f39d22fbe1c05a8c6')
pin('reviews/ordinary14-natural79-decimal-port-math-independent/result.json','a647e8417ca8e4b584193137e01ba849822bd681344b0a35cbacbefe23caa636')
pin('reviews/ordinary13-natural-residue-forced90-decimal-display-independent/check.py','e55292f6cb53418fcdffe207d5a36146386bfa2799228d8b42890bce54077d90')
pin('reviews/ordinary13-natural-residue-forced90-decimal-display-independent/result.json','4425dd86279552ff95880962b07957e4643f6e515f071ebf426f09cb47bf7ffd')
for p in ['reviews/ordinary14-natural79-decimal-port-math-independent','reviews/ordinary13-natural-residue-forced90-decimal-display-independent']:
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(D/p/'check.py')],cwd=D)==(D/p/'result.json').read_bytes()
tex=pin('equation.tex','94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635').decode();pin('equation.pdf','23a52933980352f83a19c21a0d6f349594be5f85edc85a462e25ffc83c7fd5d6')
assert r'\rho=2^{47}' in tex and r'B=\rho^{2011}' in tex and 47*2011!=67*8807
print(json.dumps({'scope':'pinned source signatures, external P72/P115 bytes and independently reviewed decimal displays; no Lean or formal PDF semantics','P72_P115_four_gzip_and_raw_payloads_identical':True,'four_port_order':['beta','K0','MC','MF'],'MF_shifted_once':True,'compact_beta_bits':values['beta'].bit_length(),'K_bits':values['K0'].bit_length(),'symbolic_K_parameter_requires_selection':True,'external_byte_to_Lean_list_not_proved_here':True,'current_root_equation_tuple_distinct':True,'lean_elaborated':False},sort_keys=True,indent=2))
