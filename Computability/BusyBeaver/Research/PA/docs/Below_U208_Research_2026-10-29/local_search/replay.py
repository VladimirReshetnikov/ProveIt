from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent

def require(v,m):
 if not v:raise RuntimeError(m)

def main():
 manifest=json.loads((P/'MANIFEST.json').read_text())
 actual={str(p.relative_to(P))for p in P.rglob('*')if p.is_file()and p.name!='MANIFEST.json'and '__pycache__'not in p.parts}
 require(actual==set(manifest),'file set')
 for rel,sha in manifest.items():require(hashlib.sha256((P/rel).read_bytes()).hexdigest()==sha,'hash '+rel)
 for inp in json.loads((P/'inputs.json').read_text()):
  lines=[l.split()for l in(P/inp['file']).read_text().splitlines()if l and not l.startswith('#')]
  require(len(lines)==416,'transition count');rows={(int(a),int(b))for a,b,w,d,z in lines};states={q for q,b in rows}
  require(len(states)==208 and rows=={(q,b)for q in states for b in(0,1)},'total binary table')
 for name in['history_results.json','compatibility_results.json','initial_history_results.json','initial_compatibility_results.json']:
  r=json.loads((P/'receipts'/name).read_text());require(r['found']is False,'negative search receipt')
 for name in['fold_neutral_results.json','compat_fold_neutral_results.json']:
  r=json.loads((P/'receipts'/name).read_text());require(r['found']==0 and r['trials']==122544,'helper search receipt')
 subprocess.run([sys.executable]+(['-O']if sys.flags.optimize else[])+['-B',str(P/'verify_neutral.py')],check=True)
 print('PASS local research integrity, table shape, frozen receipts, neutral identities')
if __name__=='__main__':main()
