import ast,gzip,hashlib,json,random,sys
from pathlib import Path
from itertools import product
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2]; E=D/'research/p64-qcube79-local-rewrite-search/search.py'; G=D/'research/ordinary13-four-square88-30/candidate.json'
assert hashlib.sha256(E.read_bytes()).hexdigest()=='4c8e09ecb5ca438123ab0ac1b6cb6e07b5d27f95c6cee651debde2ccbb438f46'
assert hashlib.sha256(G.read_bytes()).hexdigest()=='daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'
PRIME=1000000007;SAMPLES=3;SEED=0x8846
nodes={'evaluate','live_count','search','alias_and_square_sign'};T=ast.parse(E.read_bytes());defs=[n for n in T.body if isinstance(n,ast.FunctionDef) and n.name in nodes];assert {n.name for n in defs}==nodes;exec(compile(ast.Module(body=defs,type_ignores=[]),str(E),'exec'))
g=json.loads(G.read_text());rows=g['source'];vars=g['witnesses']+g['fixed_numerals'];out=g['output'];assert len(rows)==live_count(rows,out)==88
uniform=search(rows,vars,out);extra=alias_and_square_sign(rows,vars,out)
p=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';binding=p/'ACTIVE_BINDING.json';b115=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json';assert hashlib.sha256(binding.read_bytes()).hexdigest()=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf';assert hashlib.sha256(b115.read_bytes()).hexdigest()=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01';B=json.loads(binding.read_text());C=json.loads(b115.read_text());fixed={}
for n,m in B['ports'].items():
 z=(p/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip']==C['ports'][n]['sha256_gzip'];raw=gzip.decompress(z);assert hashlib.sha256(raw).hexdigest()==m['sha256_raw']==C['ports'][n]['sha256_raw'];fixed[n]=int.from_bytes(raw,'little')%PRIME
fix=search(rows,vars,out,fixed=fixed)
control=rows[:-1]+[['__neg_one__','-',0,rows[-1][2]],['__neg_two__','-',0,'__neg_one__'],[rows[-1][0],rows[-1][1],'__neg_two__',rows[-1][3]]];pos=alias_and_square_sign(control,vars,out);assert pos['aliases']
print(json.dumps({'uniform':uniform,'alias_sign':extra,'fixed':fix,'control':pos},sort_keys=True,indent=2))
