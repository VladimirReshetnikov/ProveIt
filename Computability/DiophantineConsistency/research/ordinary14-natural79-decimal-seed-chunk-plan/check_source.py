#!/usr/bin/env python3
"""Read-only coverage and arithmetic control for inert source proposals."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1];base=D/'research/ordinary14-natural79-decimal-selector-kernel-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
pin(P/'generate.py','3e0c1a66d8d84298955baff5cac62664f7485d7ab1e607f220fd2e6223677031')
manifest=json.loads(pin(P/'manifest.json','ec3c494541a0c6230cf92b5bc9f30b717cf7ccb774be64f11d11f636cdc8daac'))
seedSource=pin(base/'PrintedDecimalSeed.lean.src','90412429af931cf76323671d059993b02eef68a11df63e79de91cb01372f305d')
blocksSource=pin(base/'PrintedDecimalBlocks.lean.src','86252120c4aa90f31c6084b70507e9c67ee7602889daad73df3b0cc84a83eb3d')
pin(base/'DecimalSelectorKernel.lean.src','28ae1b56e9c9b2d83d7457d3fcbf65d0c5effe2f440fe5843ff6e2e649ab3c61')
rows=pin(D/'Lean/DiophantineConsistency/Compact44/Compact943Data.lean','10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8')
seed=seedSource.split('def printedSeed : ℕ :=\n  ',1)[1].split('\nend ',1)[0];assert seed.isdecimal() and len(seed)==15086
x=blocksSource.split('def printedBlocks : List ℕ := [\n',1)[1].split('\n]',1)[0];assert re.fullmatch(r'[0-9,\s]+',x);blocks=[int(y) for y in x.split(',')];assert len(blocks)==943
part=rows.split('-- BEGIN PINNED ORDERED ROWS\n',1)[1].split('\n-- END PINNED ORDERED ROWS',1)[0];table=[]
for line in part.splitlines():
 m=re.fullmatch(r'  \((\d+), (\d+), (\d+), (\d+)\),?',line);assert m;table.append(tuple(map(int,m.groups())))
expected=[1+2**10*(2**41-(a+2**8*b+2**17*c+2**25*d+127*2**34)) for a,b,c,d in table];assert len(expected)==943
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
N=int(seed);assert N<(10**16)**943
chunks=manifest['chunks'];assert len(chunks)==30
coverage=[];source=P/'source';assembly=pin(source/'DecimalFiniteAssembly.lean.src',manifest['assembly_sha256']);common=pin(source/'DecimalFiniteCommon.lean.src',manifest['common_sha256'])
assert {p.name for p in source.iterdir()}=={'DecimalFiniteCommon.lean.src','DecimalFiniteAssembly.lean.src'}|{c['module']+'.lean.src' for c in chunks}
for index,c in enumerate(chunks):
 start=c['start'];stop=c['stop'];width=stop-start;assert c['index']==index and start==32*index and stop==min(start+32,943) and c['module']==f'DecimalFiniteChunk{index:02d}' and c['theorem']==f'chunk{index:02d}'
 src=pin(source/(c['module']+'.lean.src'),c['sha256']);assert f'theorem {c["theorem"]} : ∀ i : Fin {width},' in src and f'printedBlocks.getD ({start}+i.val) 0 = selectorAt ({start}+i.val)' in src and f'printedBlocks.getD ({start}+i.val) 0 = seedBlockAt ({start}+i.val)' in src
 assert f'import {c["module"]}\n' in assembly and f'chunk{index:02d} ⟨' in assembly
 for n in range(start,stop):
  assert blocks[n]==expected[n] and blocks[n]==(N//((10**16)**n))%(10**16);coverage.append(n)
assert coverage==list(range(943))
for item in ('theorem all_blocks','theorem printedBlocks_eq_selectorBlocks','theorem printedSeed_eq_blocks','theorem printedSeed_eq_symbolicSeed','RadixWindowReconstruction.ofDigits_eq_of_windows'):
 assert item in assembly
assert 'theorem printedBlocks_length' in common and 'theorem printedSeed_lt' in common
print(json.dumps({'scope':'exact external finite index coverage and arithmetic controls for generated source; no Lean/typecheck/proof', 'chunk_count':len(chunks),'block_count':len(coverage),'chunk_widths':[c['stop']-c['start'] for c in chunks], 'all_943_selector_controls':True,'all_943_seed_windows':True,'disjoint_contiguous_coverage':True,'seed_and_block_lean_equalities_proved':False},indent=2,sort_keys=True))
