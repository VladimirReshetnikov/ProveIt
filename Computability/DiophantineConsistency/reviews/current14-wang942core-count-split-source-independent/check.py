from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];d=root/'research/current14-wang942core-count-split-draft';old=root/'research/current14-wang942core-staged-draft'
pins={'WangTiles942Core.lean':'10b17e29974c474345eb6d8ac574f8b24324eca5955a12170841164f8663eec5','WangTiles942CoreA.lean':'b2813e0e8a82ebb2fdded05cc36bec61818a68119b189072358e8b24f75b82d1','WangTiles942CoreB.lean':'4e1615aeae5b3edb3c95d33e055ae6299eac286184b98c2b726c8d4efac9ecc8','WangTiles942CountsFalse.lean':'068200cedd540a02951becce3d5cef7444be6116ce30f8efd1df844e0ff905e9','WangTiles942CountsTrue.lean':'654ffbb4384527e91e9b4ebb047b267a8463c701a3ba97269ff0994dc39a3eee'}
for n,h in pins.items():assert hashlib.sha256((d/n).read_bytes()).hexdigest()==h,n
for n in ('WangTiles942Core.lean','WangTiles942CoreA.lean'):assert (d/n).read_bytes()==(old/n).read_bytes()
a=(old/'WangTiles942CoreB.lean').read_text();imp='import DiophantineConsistency.WangTiles942CoreA\n';assert a.count(imp)==1
a=a.replace(imp,imp+'import DiophantineConsistency.WangTiles942CountsFalse\nimport DiophantineConsistency.WangTiles942CountsTrue\n');oldproof='theorem target_counts : (targets false).card = 45 ∧ (targets true).card = 199 := by\n  decide +kernel\n';assert a.count(oldproof)==1;a=a.replace(oldproof,oldproof.replace('  decide +kernel','  exact ⟨target_counts_false, target_counts_true⟩'));assert a==(d/'WangTiles942CoreB.lean').read_text()
for side,value in [('False',45),('True',199)]:
 name=side.lower();text=(d/f'WangTiles942Counts{side}.lean').read_text();assert text==f'''import DiophantineConsistency.WangTiles942CoreA\n\nnamespace DiophantineConsistency.WangTiles942\nset_option Elab.async false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 20000000\nset_option exponentiation.threshold 1024\n\ntheorem target_counts_{name} : (targets {name}).card = {value} := by\n  decide +kernel\n\nend DiophantineConsistency.WangTiles942\n#print axioms DiophantineConsistency.WangTiles942.target_counts_{name}\n'''
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-wang942core-staged-failure-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_SOURCE_DELTA_REVIEW','target_counts':['false = 45','true = 199'],'lean_run':False,'scope':'Count split source only; child feasibility and join uncompiled'},indent=2))
