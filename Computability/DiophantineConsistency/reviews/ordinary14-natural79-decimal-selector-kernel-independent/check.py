#!/usr/bin/env python3
"""Independent finite packing and source-interface audit; never runs Lean."""
from pathlib import Path
import hashlib,json,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
sys.set_int_max_str_digits(0)
D=Path(__file__).resolve().parents[2];T=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean/Init/Tactics.lean')
files={
 'kernel':('research/ordinary14-natural79-decimal-selector-kernel-draft/DecimalSelectorKernel.lean.src','28ae1b56e9c9b2d83d7457d3fcbf65d0c5effe2f440fe5843ff6e2e649ab3c61'),
 'blocks':('research/ordinary14-natural79-decimal-selector-kernel-draft/PrintedDecimalBlocks.lean.src','86252120c4aa90f31c6084b70507e9c67ee7602889daad73df3b0cc84a83eb3d'),
 'numeral':('research/ordinary14-natural79-decimal-selector-kernel-draft/PrintedDecimalSeed.lean.src','90412429af931cf76323671d059993b02eef68a11df63e79de91cb01372f305d'),
 'candidate_seed':('research/ordinary14-natural79-decimal-render-candidate/DECIMAL_SEED.txt','8c85329f040c7a4d41d521deee0dec970191ff59e08ccf5487e32655dc09a297'),
 'rows':('Lean/DiophantineConsistency/Compact44/Compact943Data.lean','10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8'),
 'selector':('Lean/DiophantineConsistency/Compact44/CompactCoefficientMass.lean','1dad41ebf3fe6c9c68b6f6d76bd6d1a42f318ca75eb6f107d3bcd0407246b592'),
 'radix':('Lean/DiophantineConsistency/Compact44/SparseRadix.lean','1e9f64186090cc13c77c8f704ff0291928e35700390833c70333e5fc386f65fa'),
 'param_kernel':('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernelOpaque.lean','8ae9ed11d9e7408e4fd71555569181b0fb785f24f3177facc6c6c997d0d5e615'),
 'low_recipe':('Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean','f93993e8b4badb6518d8ac6e575d406f322d7205b7d95c17c185103510b474c2'),
 'author_result':('research/ordinary14-natural79-decimal-selector-kernel-draft/result.json','b18e69a3ebbefbce14ab508809e5537dd47dbee3d061b69de6f89d0fde2f0ff1')}
s={}
for name,(p,h) in files.items():
 raw=(D/p).read_bytes();assert hashlib.sha256(raw).hexdigest()==h,name;s[name]=raw.decode()
assert hashlib.sha256(T.read_bytes()).hexdigest()=='0eae8de34543a9985025264c213f5c4eb2a4697316141885a136a90e8dc4b441'
assert '(try (with_reducible rfl))' in T.read_text()
seed=s['candidate_seed'].strip();assert re.fullmatch(r'[1-9]\d{15085}',seed)
literal=s['numeral'].split('def printedSeed : ℕ :=\n  ',1)[1].split('\nend ',1)[0]
assert literal==seed
body=s['blocks'].split('def printedBlocks : List ℕ := [\n',1)[1].split('\n]',1)[0]
assert re.fullmatch(r'[0-9,\s]+',body);blocks=[int(n.strip()) for n in body.split(',')]
assert len(blocks)==943 and all(0<=n<10**16 for n in blocks)
# Independent right-to-left Euclidean extraction, not decimal concatenation.
remaining=int(seed);recovered=[]
for _ in range(943):remaining,d=divmod(remaining,10**16);recovered.append(d)
assert remaining==0 and recovered==blocks and len(seed)==15086
ordered=s['rows'].split('-- BEGIN PINNED ORDERED ROWS\n',1)[1].split('\n-- END PINNED ORDERED ROWS',1)[0]
table=[]
for line in ordered.splitlines():
 m=re.fullmatch(r'\s*\((\d+), (\d+), (\d+), (\d+)\),?',line);assert m,line
 table.append(tuple(map(int,m.groups())))
assert len(table)==943
assert 't.1 + 2^8*t.2.1 + 2^17*t.2.2.1 + 2^25*t.2.2.2 + 127*2^34' in s['selector']
assert '1 + 2^10 * (2^41 - value t)' in s['selector']
values=[a+2**8*b+2**17*c+2**25*d+127*2**34 for a,b,c,d in table]
assert all(0<=v<=2**41 for v in values)
selectors=[1+2**10*(2**41-v) for v in values]
assert selectors==blocks and 1+2**51<10**16
k=s['kernel'];flat=lambda x:re.sub(r'\s+',' ',x)
assert 'def selectorBlocks : List ℕ := List.ofFn (fun i : Fin 943 =>' in k
assert 'def symbolicSeed : ℕ := Nat.ofDigits (10^16) selectorBlocks' in k
assert 'def block (seed : ℕ) (i : Fin 943) : ℕ := (seed / (10^16)^i.val) % (10^16)' in k
assert 'theorem digit_ofDigits (b : ℕ) (L : List ℕ) (hb : 0 < b)' in s['radix']
assert '(hL : ∀ x ∈ L, x < b)' in s['radix'] and '(Nat.ofDigits b L / b ^ i) % b = L[i]' in s['radix']
assert 'theorem selectorBlocks_bounded : ∀ x ∈ selectorBlocks, x < 10^16' in k
assert 'SparseRadix.digit_ofDigits (10^16) selectorBlocks (by norm_num)' in k
assert 'selectorBlocks_bounded i.val hi' in k
assert 'r^8849 = r^8807*r^42' in k and '(pow_add r 8807 42)' in k
assert 'CompactConcreteMask.concrete_recipe.symm' in k
assert '(hpack : Natural79PrintedDecimalSeedDraft.printedSeed =' in k and '(hblocks : Natural79PrintedDecimalBlocksDraft.printedBlocks = selectorBlocks)' in k
assert 'exact hpack.trans (congrArg (Nat.ofDigits (10^16)) hblocks)' in k
assert '(hseed : Natural79PrintedDecimalSeedDraft.printedSeed = symbolicSeed)' in k
assert not re.search(r'^\s*(?:axiom|opaque)\b|\b(?:sorry|admit)\b',k,re.M)
assert len(re.findall(r'^#print axioms ',k,re.M))==7
print(json.dumps({'scope':'independent external exact arithmetic and bounded source-interface review; no Lean proof or provider authentication',
 'inputs':{n:{'path':p,'sha256':h} for n,(p,h) in sorted(files.items())},
 'toolchain_tactics_source_sha256':'0eae8de34543a9985025264c213f5c4eb2a4697316141885a136a90e8dc4b441',
 'digits':len(seed),'blocks':len(blocks),'radix':10**16,'leading_decimal_padding':2,
 'selector_min':min(selectors),'selector_max':max(selectors),'uniform_bound':1+2**51,
 'independent_euclidean_extraction_matches_blocks':True,'all_blocks_match_source_table':True,
 'seed_equalities_remain_explicit_hypotheses':True,'axiom_reports_executed':False},indent=2,sort_keys=True))
