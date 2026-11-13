#!/usr/bin/env python3
"""Read-only exact decimal-port comparison from displayed formulas and Lean source."""
from pathlib import Path
import gzip,hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-natural79-decimal-render-candidate'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(str(p),sha(b));return b
tex=pin(P/'equation.tex','a9a6ae35d88e3f842d5493fbe6c7f6460285a3d3ae211a40c6b0375ae350ec20').decode()
seed=pin(P/'DECIMAL_SEED.txt','8c85329f040c7a4d41d521deee0dec970191ff59e08ccf5487e32655dc09a297').decode().strip()
report=json.loads(pin(P/'result.json','38220702aeef03b916e7188a9bb76a213d3b9606d386dd15c7072aeb9e2711f8'))
bridge=pin(P/'Natural79DecimalPortBridge.lean.src','137ee4023ab657552c329e8ef8c2d38afab9c4e6c0d790b50b7080361df6b1cd').decode()
model=pin(D/'Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean','379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46').decode()
endpoint=pin(D/'research/ordinary14-natural79-corrected-reflection-overlay/source/Natural79Endpoint.lean.src','9b527ff7a8b6e166869f2565b83a8c37956680d538c49557de9c82ea1a6041e6').decode()
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in model
assert 'def expression : Expr (Fin 14) := (P79NaturalForcedW.graph CompactSymbolicModelIff.p).output' in endpoint
assert '(![beta,K,low,shiftedHigh] : Fin 4 → ℕ)' in bridge
assert '(hb : beta = CompactFixedBeta.betaNat)' in bridge and '(hk : K = paramKernel rho)' in bridge
assert '(hl : low = lowNat)' in bridge and '(hh : shiftedHigh = CompactFixedBeta.betaNat + highNat)' in bridge
src={}
files={'Compact943Data':'10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8',
 'CompactCoefficientMass':'1dad41ebf3fe6c9c68b6f6d76bd6d1a42f318ca75eb6f107d3bcd0407246b592',
 'CompactSymbolicKernel':'9b2b73430cbf4578ef4b4c7d4658c9526b7ebdc423263470df907a16b454ba55',
 'CompactSymbolicKernelOpaque':'8ae9ed11d9e7408e4fd71555569181b0fb785f24f3177facc6c6c997d0d5e615',
 'CompactConcreteMask':'f93993e8b4badb6518d8ac6e575d406f322d7205b7d95c17c185103510b474c2',
 'CompactListMask':'34c4d38c265160155a7fa3f99ea3af692c5f3be10b7b77cac211afc199953d4b',
 'CompactHighPopulation':'b1e962aed2f9fc2b49533a52f3508a84af4d433c4a9fae210540e085056dab1d',
 'CompactSymbolicPorts':'0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414',
 'CompactFixedBeta':'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea'}
for n,h in files.items():src[n]=pin(D/('Lean/DiophantineConsistency/Compact44/'+n+'.lean'),h).decode()
for n,x in [('CompactFixedBeta','def betaNat : ℕ := 2^(67*8807)-1'),
 ('CompactSymbolicPorts','def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]'),
 ('CompactSymbolicPorts','Nat.ofDigits (2^67) CompactHighPopulation.highDigits'),
 ('CompactSymbolicPorts','Nat.ofDigits (2^67) (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support)'),
 ('CompactCoefficientMass','def selector (t : Nat × Nat × Nat × Nat) : Nat := 1 + 2^10 * (2^41 - value t)'),
 ('CompactCoefficientMass','t.1 + 2^8*t.2.1 + 2^17*t.2.2.1 + 2^25*t.2.2.2 + 127*2^34'),
 ('CompactSymbolicKernelOpaque','r^30+r^62+r^1100+r^2201 +'),
 ('CompactSymbolicKernelOpaque','(∑ i : Fin 943, CompactCoefficientMass.selector (Compact943Data.row i) *'),
 ('CompactSymbolicKernelOpaque','(r^(4393-i.val)+r^(5495-i.val))'),
 ('CompactSymbolicKernelOpaque','(∑ i : Fin 41, (2^(10+i.val):ℕ) * (r^(4393-position i)+r^(5495-position i)))'),
 ('CompactSymbolicKernelOpaque','r^8807*r^42'),
 ('CompactSymbolicKernel','def rho : ℕ := 2^67'),
 ('CompactListMask','if j=special then B-4 else if j∈S then B-2 else B-1')]:assert x in src[n],(n,x)
assert r'\rho=2^{67}' in tex and r'\beta=\rho^{8807}-1' in tex
assert r'd_j=\lfloor P/10^{16j}\rfloor\bmod 10^{16}' in tex
part=tex.split(r'\fontsize{6}{7}\selectfont\ttfamily',1)[1].split(r'\endgroup',1)[0]
decimal_lines=[line[:-4] for line in part.splitlines() if line.endswith(r'\par')]
assert decimal_lines and all(re.fullmatch(r'[0-9]+',x) for x in decimal_lines)
assert ''.join(decimal_lines)==seed and len(seed)==15086 and sha(seed.encode())==report['decimal_seed_sha256']
# Derive selectors independently from the pinned source row tuples and compare
# to the right-to-left 16-digit blocks displayed in TeX, including leading zeros.
body=src['Compact943Data'].split('-- BEGIN PINNED ORDERED ROWS\n',1)[1].split('\n-- END PINNED ORDERED ROWS',1)[0]
table=[tuple(map(int,m)) for m in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)',body)]
assert len(table)==943 and all(len(row)==4 for row in table)
expected=[1+2**10*(2**41-(a+2**8*b+2**17*c+2**25*d+127*2**34)) for a,b,c,d in table]
assert all(0<x<10**16 for x in expected)
padded=seed.zfill(16*943);assert len(padded)==16*943
blocks=[int(padded[len(padded)-16*(i+1):len(padded)-16*i]) for i in range(943)]
assert blocks==expected
# Parse the displayed lambda list, preserving order, and compare to Lean.
slottext=tex.split(r'\[\begin{gathered}',1)[1].split(r'\end{gathered}\]',1)[0]
slots=[int(x) for x in re.findall(r'\d+',slottext)]
lean_slots=[int(x) for x in re.search(r'^def slots : List ℕ := \[([0-9,]+)\]',src['CompactSymbolicKernel'],re.M).group(1).split(',')]
assert len(slots)==41 and slots==lean_slots
for x in (r'K={}&\rho^{30}+\rho^{62}+\rho^{1100}+\rho^{2201}+\rho^{8849}',
 r'\sum_{j=0}^{942}d_j(\rho^{4393-j}+\rho^{5495-j})',
 r'\sum_{j=0}^{40}2^{10+j}(\rho^{4393-\lambda_j}+\rho^{5495-\lambda_j})',
 r'\mu=\beta-\sum_{k\in S}\rho^k-2\rho^{1063}',r'\omega=\beta+H'):
 assert x in tex,x
B=2**67;beta=B**8807-1
K=sum(B**j for j in (30,62,1100,2201,8849))
K+=sum(blocks[j]*(B**(4393-j)+B**(5495-j)) for j in range(943))
K+=sum(2**(10+j)*(B**(4393-slots[j])+B**(5495-slots[j])) for j in range(41))
# Verify the displayed set against the source set, then construct lowNat by
# little-endian radix digits rather than the TeX subtraction formula.
Stext=tex.split(r'\begin{split}S=',1)[1].split(r'\end{split}',1)[0]
intervals=[tuple(map(int,x)) for x in re.findall(r'\[(\d+),(\d+)\]',Stext)]
assert intervals==[(0,942),(983,992),(1003,1011),(1013,1031)]
assert r'\{1063,1064,1095,2195,3296\}' in Stext and r'\setminus\{1\}' in Stext
assert 'range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032' in src['CompactConcreteMask']
assert '{1063,1064,1095,2195,3296}) \\ {1}' in src['CompactConcreteMask']
S=set().union(*(set(range(a,b+1)) for a,b in intervals),{1063,1064,1095,2195,3296})-{1}
mu=0
for j in reversed(range(8807)):
 mu=(mu<<67)+(B-4 if j==1063 else B-2 if j in S else B-1)
assert mu==beta-sum(1<<(67*j) for j in S)-2*(1<<(67*1063))
# Verify the literal H formula and independently build the source run list.
for x in (r'H={}&4+\sum_{k=1013}^{1022}\rho^k+\sum_{k=1065}^{1073}\rho^k+\rho^{2195}+\rho^{3296}',
 r'(2^{51}-2)(\rho^{4393}+\rho^{5495})',r'(2^{65}-1)\sum_{k=8792}^{8804}\rho^k',r'(2^{19}-1)\rho^{8805}'):
 assert x in tex,x
high_source=src['CompactHighPopulation']
for x in ('def mu : ℕ := 2^51-2','def padding : ℕ := 2^65-1','def lastPadding : ℕ := 2^19-1',
 'List.replicate 1012 0 ++ List.replicate 10 1','List.replicate 3296 0 ++ List.replicate 13 padding'):
 assert x in high_source,x
H=4+sum(B**j for j in range(1013,1023))+sum(B**j for j in range(1065,1074))+B**2195+B**3296
H+=(2**51-2)*(B**4393+B**5495)+(2**65-1)*sum(B**j for j in range(8792,8805))+(2**19-1)*B**8805
parts=high_source.split('def highDigits : List ℕ :=',1)[1].split('\ntheorem digits_length',1)[0].split('++')
atoms={'mu':2**51-2,'padding':2**65-1,'lastPadding':2**19-1}
def atom(x):
 x=x.strip()
 return int(x) if x.isdecimal() else atoms[x]
runs=[]
for part in parts:
 part=part.strip()
 m=re.fullmatch(r'List\.replicate\s+(\d+)\s+(\w+)',part)
 if m:runs.extend([atom(m.group(2))]*int(m.group(1)))
 else:
  assert part.startswith('[') and part.endswith(']'),part
  runs.extend(atom(x) for x in part[1:-1].split(','))
assert len(runs)==8807 and H==sum(x*B**j for j,x in enumerate(runs) if x)
omega=beta+H
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding=json.loads(pin(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
expected_values={'beta':beta,'K0':K,'MC':mu,'MF':omega};hashes={}
for n,x in expected_values.items():
 m=binding['ports'][n];raw=gzip.decompress(pin(p72/m['path'],m['sha256_gzip']))
 assert len(raw)==m['raw_bytes'] and sha(raw)==m['sha256_raw'] and int.from_bytes(raw,'little')==x
 hashes[n]=m['sha256_raw']
assert report['port_values_match_retained_gzip_bytes']==hashes and report['fixed_mf_shifted_once'] is True
print(json.dumps({'scope':'exact source and displayed TeX arithmetic versus external P72 bytes; no Lean/PDF semantics',
 'seed_decimal_digits':len(seed),'selector_blocks':len(blocks),'ordered_kernel_slots':len(slots),
 'low_mask_exception_digit':1063,'high_digit_count':len(runs),'omega_beta_additions':1,
 'four_raw_hashes':hashes,'lean_executed':False},sort_keys=True,indent=2))
