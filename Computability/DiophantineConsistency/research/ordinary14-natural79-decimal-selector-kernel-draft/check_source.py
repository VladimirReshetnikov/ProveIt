#!/usr/bin/env python3
"""Finite external pin/block check only; no Lean, compiler or staging."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
seed=pin(D/'research/ordinary14-natural79-decimal-render-candidate/DECIMAL_SEED.txt','8c85329f040c7a4d41d521deee0dec970191ff59e08ccf5487e32655dc09a297').strip()
printed=pin(P/'PrintedDecimalSeed.lean.src','90412429af931cf76323671d059993b02eef68a11df63e79de91cb01372f305d')
blocks_text=pin(P/'PrintedDecimalBlocks.lean.src','86252120c4aa90f31c6084b70507e9c67ee7602889daad73df3b0cc84a83eb3d')
bridge=pin(P/'DecimalSelectorKernel.lean.src','28ae1b56e9c9b2d83d7457d3fcbf65d0c5effe2f440fe5843ff6e2e649ab3c61')
rows=pin(D/'Lean/DiophantineConsistency/Compact44/Compact943Data.lean','10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8')
mass=pin(D/'Lean/DiophantineConsistency/Compact44/CompactCoefficientMass.lean','1dad41ebf3fe6c9c68b6f6d76bd6d1a42f318ca75eb6f107d3bcd0407246b592')
radix=pin(D/'Lean/DiophantineConsistency/Compact44/SparseRadix.lean','1e9f64186090cc13c77c8f704ff0291928e35700390833c70333e5fc386f65fa')
assert len(seed)==15086 and seed.isdecimal() and printed.split('def printedSeed : ℕ :=\n  ',1)[1].split('\nend ',1)[0]==seed
content=blocks_text.split('def printedBlocks : List ℕ := [\n',1)[1].split('\n]',1)[0]
assert re.fullmatch(r'[0-9,\s]+',content); blocks=[int(x.strip()) for x in content.split(',')];assert len(blocks)==943 and all(0<=v<10**16 for v in blocks)
assert ''.join(f'{x:016d}' for x in reversed(blocks)).lstrip('0')==seed
inside=rows.split('-- BEGIN PINNED ORDERED ROWS\n',1)[1].split('\n-- END PINNED ORDERED ROWS',1)[0]; table=[]
for line in inside.splitlines():
 m=re.fullmatch(r'  \((\d+), (\d+), (\d+), (\d+)\),?',line);assert m;table.append(tuple(map(int,m.groups())))
assert len(table)==943 and 't.1 + 2^8*t.2.1 + 2^17*t.2.2.1 + 2^25*t.2.2.2 + 127*2^34' in mass
assert '1 + 2^10 * (2^41 - value t)' in mass
selectors=[1+2**10*(2**41-(a+2**8*b+2**17*c+2**25*d+127*2**34)) for a,b,c,d in table]
assert selectors==blocks and 'theorem digit_ofDigits' in radix
for n in ('selector_lt_decimal_base','symbolic_block','decimalKernel_of_blocks','seed_equality_of_finite_checks','printed_decimalKernel_of_seed_equality','decimalLow_eq_lowNat'):
 assert 'theorem '+n in bridge and '#print axioms Natural79DecimalSelectorKernelDraft.'+n in bridge
assert '(hpack :' in bridge and '(hblocks :' in bridge and '(hseed :' in bridge
print(json.dumps({'scope':'external exact finite source/list/decimal comparison; no Lean proof, axiom check or physical-file semantics','decimal_digits':len(seed),'decimal_blocks':len(blocks),'all_blocks_in_decimal_base':True,'all_blocks_match_source_selector_transcription':True,'seed_equals_packed_blocks_externally':True,'lean_seed_equalities_remain_hypotheses':True,'unexpanded_compact_ports':True},indent=2,sort_keys=True))
