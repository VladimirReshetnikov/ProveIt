import ast,io,tokenize,gzip,json,hashlib,zipfile
from pathlib import Path
SKIP={tokenize.ENCODING,tokenize.COMMENT,tokenize.NL,tokenize.NEWLINE,tokenize.INDENT,tokenize.DEDENT,tokenize.ENDMARKER}
class Strip(ast.NodeTransformer):
 def clean(self,node):
  self.generic_visit(node)
  if node.body and isinstance(node.body[0],ast.Expr) and isinstance(node.body[0].value,ast.Constant) and isinstance(node.body[0].value.value,str):node.body=node.body[1:]
  return node
 visit_Module=clean;visit_FunctionDef=clean;visit_AsyncFunctionDef=clean;visit_ClassDef=clean
sources={}; archives=set()
def add(raw,name):
 sha=hashlib.sha256(raw).hexdigest()
 if sha not in sources:
  try:
   tree=ast.fix_missing_locations(Strip().visit(ast.parse(raw)))
   normalized=(ast.unparse(tree)+'\n').encode()
   sources[sha]=dict(sha=sha,paths=[],raw_bytes=len(raw),bytes=len(normalized),tokens=sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),ast=sum(1 for _ in ast.walk(tree)),gzip9=len(gzip.compress(raw,compresslevel=9,mtime=0)))
  except Exception:return
 sources[sha]['paths'].append(name)
def archive(raw,name):
 sha=hashlib.sha256(raw).hexdigest()
 if sha in archives:return
 archives.add(sha)
 with zipfile.ZipFile(io.BytesIO(raw)) as z:
  for item in z.infolist():
   if item.filename.endswith('.py'):add(z.read(item),name+'!'+item.filename)
   elif item.filename.endswith('.zip'):archive(z.read(item),name+'!'+item.filename)
for p in Path('ProveIt/docs/drafts').glob('*.zip'):archive(p.read_bytes(),str(p))
rows=list(sources.values())
Path('baseline_audit_work/all_metrics.json').write_text(json.dumps(rows,indent=2)+'\n')
small=[x for x in rows if x['bytes']<=616 or x['tokens']<=268 or x['ast']<=300]
print('distinct sources',len(rows),'distinct archives',len(archives),'boundary sources',len(small))
for x in sorted(small,key=lambda r:r['bytes']):print(x['sha'][:12],*[x[k] for k in ['tokens','ast','bytes','raw_bytes','gzip9']],x['paths'][0])
