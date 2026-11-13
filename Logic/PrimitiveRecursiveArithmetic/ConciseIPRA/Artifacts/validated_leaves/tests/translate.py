from pathlib import Path
import ast,copy,json,subprocess,sys,tokenize,io
OUT=Path(__file__).resolve().parent.parent

def opening(a,k,image=None,d=0):
 if type(a) is list:return [opening(b,k,image,d+5-len(a)) for b in a]
 if type(a) is not int:raise TypeError
 if k<=a<d:return a
 return d%2 and opening(image,k,d=3)

def expr(t):
 if type(t) is list:return [expr(x) for x in t]
 return t or 1

def convert(data):
 pending=copy.deepcopy(data[:-1]);goal=copy.deepcopy(data[-1]);emitted=[];kinds=[]
 source=(OUT/'reference/controls/direct_leaves_strict.py').read_text();tree=ast.parse(source);ns={}
 exec(compile(ast.Module(body=tree.body[:2],type_ignores=[]),'<old direct leaves>','exec'),ns)
 checker=ns['c']
 def pop():return pending.pop()
 ns['q']=pop
 def wrapped(g,a,k=0,v=0):
  validated=opening(a,k)
  if validated in g:
   emitted.append([0,0,1,1]);kinds.append('hyp');return True
  old=copy.deepcopy(pending[-1]);m,s,u,t=old
  H=[[s and [s],u,t],opening(t,k,[s,u,t],3) if s else u]
  if validated==H:
   emitted.append([0,expr(s) if s else 0,expr(u),expr(t)]);kinds.append('comp')
  elif not m:
   emitted.append([0,s,2 if u==0 else 0,expr(t)]);kinds.append('intro')
  elif len(m) in(2,3):
   emitted.append([expr(m),expr(s) if s else 0,expr(u),expr(t)]);kinds.append('elim')
  else:
   emitted.append([expr(m),s,u,t]);kinds.append('open')
  return checker(g,a,k,v)
 ns['c']=wrapped
 wrapped([0],goal,v=1)
 return list(reversed(emitted))+[expr(goal)],kinds

def accepts(checker,data):
 p=subprocess.run([sys.executable,str(checker)],input=json.dumps(data),text=True,capture_output=True,timeout=5)
 return p.returncode==0 and p.stdout=='ACCEPT\n',p.stderr[-600:]

if __name__=='__main__':
 cases=[]
 for p in sorted((OUT/'reference/source_fixtures').glob('*.json')):
  source=json.loads(p.read_text());new,kinds=convert(source)
  out=OUT/'fixtures'/p.name;out.parent.mkdir(exist_ok=True);out.write_text(json.dumps(new,separators=(',',':'))+'\n')
  ok,err=accepts(OUT/'code/checker_strict606.py',new)
  cases.append({'file':p.name,'accepted':ok,'kinds':{x:kinds.count(x) for x in set(kinds)},'error':err if not ok else ''})
 print(json.dumps(cases,indent=2))
 (OUT/'evidence/translation_results.json').write_text(json.dumps(cases,indent=2)+'\n')

if __name__ == "__main__" and not all(x["accepted"] for x in cases):
 raise SystemExit("Translation failed")
