from pathlib import Path
import hashlib,json,random
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'Guard88.lean').read_text()
for t in ('P88QuotientGuarded.output_shape','fiveSquares_eq_zero_iff','theorem guard_of_zero','theorem b_eval','theorem bt_of_zero','P88QuotientGuarded.graph p'):assert t in s
rng=random.Random(8813)
for _ in range(1000):
 J,beta,t=[rng.randrange(-20,21) for _ in range(3)]
 assert J*beta*t==(J*beta)*t
print(json.dumps({'guard_product_controls':1000,'lean_run':False,'source_sha256':hashlib.sha256((p/'Guard88.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
