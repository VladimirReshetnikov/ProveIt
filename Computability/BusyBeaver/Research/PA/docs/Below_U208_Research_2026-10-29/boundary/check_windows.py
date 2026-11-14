from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent
B=R/'baseline'
def need(c,m):
 if not c:raise ValueError(m)
def check(path):
 o=json.loads(path.read_text());need(o['radius']==3,'radius')
 need(o['table_sha256']==hashlib.sha256((B/'machine/u208.native.tm').read_bytes()).hexdigest(),'table binding')
 need(o['source_sha256']==hashlib.sha256((B/'machine/sites.json').read_bytes()).hexdigest(),'source binding')
 need(o['engine_sha256']==hashlib.sha256((B/'code/runtime/native_symbolic.py').read_bytes()).hexdigest(),'engine binding')
 rows=[line.split() for line in (B/'machine/u208.native.tm').read_text().splitlines() if line and not line.startswith('#')]
 states={int(v[0]) for v in rows};need(len(states)==208 and set(map(int,o['contexts']))==states,'states')
 for q,a in o['contexts'].items():need(a==sorted(set(a)) and a and all(type(x)is int and 0<=x<128 for x in a),'window shape')
 for q in o['conservatively_broad_states']:need(o['contexts'][str(q)]==list(range(128)),'compressed interiors')
 need(o['startup_steps']==48140,'startup')
 return {'file':path.name,'states':208,'windows':sum(map(len,o['contexts'].values())),'cases':o['cases'],'broad_states':len(o['conservatively_broad_states'])}
if __name__=='__main__':
 r=[check(R/'windows.json')]
 if(R/'specialized_windows.json').exists():r.append(check(R/'specialized_windows.json'))
 print(json.dumps({'status':'WINDOW_METADATA_AND_BINDINGS_PASS','results':r,'scope':'Receipt structure/binding check, not rederivation of symbolic projection.'},indent=2))
