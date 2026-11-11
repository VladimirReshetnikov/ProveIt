from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];orig=root/'Lean/DiophantineConsistency/SplitGeometry59.lean';draft=root/'research/current14-splitgeometry59-quadratic-partition-draft/SplitGeometry59.lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(orig)=='5363314c08408aaaa8539933132084e6bc7315372b6c6ddaf05e756b838b471d' and sha(draft)=='191c880fd6543e036c832333073aada2720c5f4b0f014ada4bc2c15e5400700e'
a=orig.read_text();b=draft.read_text();assert 'def targets : Fin 22 → ℕ' in a and 'def quadraticIndices : Fin 22 → Finset (Fin 39)' in a and 'def weights : Fin 31 → ℕ' in a
start='private theorem quadratic_cross_near : ∀ k l, k ≠ l →\n    targets k ≤ targets l+232 → targets l ≤ targets k+232 →\n    ∀ a ∈ quadraticIndices k, ∀ i j : Fin 31,\n      weights i + weights j + (targets k - pairWeight weights (activePair a)) ≠\n        targets l := by decide +kernel\n';assert a.count(start)==1
helpers=''
for k in range(22):
 t=f'({k} : Fin 22)';helpers+=f'private theorem quadratic_cross_near_{k:02} : ∀ l, {t} ≠ l →\n    targets {t} ≤ targets l+232 → targets l ≤ targets {t}+232 →\n    ∀ a ∈ quadraticIndices {t}, ∀ i j : Fin 31,\n      weights i + weights j + (targets {t} - pairWeight weights (activePair a)) ≠\n        targets l := by decide +kernel\n\n'
assembly=start.replace(' := by decide +kernel\n',' := by\n  intro k\n  fin_cases k <;> first\n'+''.join(f'    | exact quadratic_cross_near_{k:02}\n' for k in range(22)))
assert a.replace(start,helpers+assembly)==b
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-coherent-extension-refactor-retry02-failure-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_SOURCE_ONLY','cases':22,'indices':'0..21 exactly','lean_run':False,'scope':'Private proof partition; elaboration and memory untested'},indent=2))
