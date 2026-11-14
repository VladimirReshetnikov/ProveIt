"""Re-establish every recorded row identity; not a replay of exhaustive synthesis."""
from pathlib import Path
import json,hashlib
from history_search import read,histories,exact
P=Path(__file__).resolve().parent

def require(v,msg):
 if not v:raise RuntimeError(msg)

def main():
 result=[]
 for inp in json.loads((P/'inputs.json').read_text()):
  path=P/inp['file'];require(hashlib.sha256(path.read_bytes()).hexdigest()==inp['sha256'],'input hash')
  t=read(path);ctx,_=histories(t,12);rows=json.loads((P/(inp['name']+'_neutral_rows.json')).read_text());require(len(rows)==inp['neutral_rows'],'row count');cases=0;branches=0
  for q,b,w,d,z in rows:
   require((q,b)in t and(w,d,z)!=t[q,b],'nontrivial known row');nt=dict(t);nt[q,b]=(w,d,z)
   for c in ctx[q]:
    ex=exact(t,nt,q,q,c,b,40);require(ex is not None,'failed identity');cases+=1;branches+=len(ex)
  result.append({'input':inp['name'],'identities':len(rows),'history_context_checks':cases,'symbolic_branches':branches})
 print(json.dumps({'status':'PASS','results':result},indent=2))
if __name__=='__main__':main()
