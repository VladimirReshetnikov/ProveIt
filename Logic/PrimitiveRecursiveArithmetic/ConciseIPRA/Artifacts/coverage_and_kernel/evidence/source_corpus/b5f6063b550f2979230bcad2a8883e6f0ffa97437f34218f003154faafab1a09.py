# HISTORICAL WORKSPACE SCRIPT: use code/audit_corpus.py for portable offline reproduction.
import ast,hashlib,io,json,platform,tokenize,zipfile
from pathlib import Path
ROOT=Path('/workspace/scratch/28113c11dba3')
IGNORE={tokenize.ENCODING,tokenize.COMMENT,tokenize.NL,tokenize.NEWLINE,tokenize.INDENT,tokenize.DEDENT,tokenize.ENDMARKER}
class Strip(ast.NodeTransformer):
 def clean(self,n):
  self.generic_visit(n)
  if n.body and isinstance(n.body[0],ast.Expr) and isinstance(n.body[0].value,ast.Constant) and isinstance(n.body[0].value.value,str):n.body=n.body[1:]
  return n
 visit_Module=visit_FunctionDef=visit_AsyncFunctionDef=visit_ClassDef=clean
rows=[];errors=[];archives=[]
def scan(raw,path):
 with zipfile.ZipFile(io.BytesIO(raw)) as z:
  for n in z.namelist():
   if n.endswith('.zip'):
    scan(z.read(n),path+'!'+n)
   if n.endswith('.py'):
    b=z.read(n)
    try:
     s=b.decode('utf8');t=ast.fix_missing_locations(Strip().visit(ast.parse(s)));norm=ast.unparse(t)+'\n'
     row={'path':path+'!'+n,'sha256':hashlib.sha256(b).hexdigest(),'tokens':sum(x.type not in IGNORE for x in tokenize.generate_tokens(io.StringIO(norm).readline)),'ast':sum(1 for x in ast.walk(t)),'bytes':len(norm.encode()),'raw_bytes':len(b),'has_public_json_input':'load(open(0))' in norm or 'loads(input(' in norm,'has_accept':'ACCEPT' in norm,'has_reject':'REJECT' in norm}
     rows.append(row)
    except Exception as e:errors.append({'path':path+'!'+n,'error':str(e)})
for p in sorted((ROOT/'proveit/docs/drafts').glob('*.zip')):
 b=p.read_bytes();archives.append({'name':p.name,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'git_blob_sha1':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()});scan(b,p.name)
candidates=[x for x in rows if x['has_public_json_input'] and x['has_accept']]
mins={k:min(x[k] for x in candidates) for k in ['tokens','ast','bytes']}
result={'commit':'2fdcf5bf988bead821c416649f713f98b7ed8776','runtime':platform.python_version(),'archive_count':len(archives),'archives':archives,'source_occurrences':len(rows),'unique_source_hashes':len({x['sha256'] for x in rows}),'errors':errors,'preliminary_public_checker_filter':'Contains load(open(0)) or loads(input(...), plus ACCEPT. Classification reviewed separately.','candidate_envelope':mins,'attainers':{k:[x for x in candidates if x[k]==mins[k]] for k in mins},'rows':rows}
out=ROOT/'audit_experiments/current_corpus_metrics.json';out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['rows','archives']},indent=2))
print('ALL SOURCES UNDER 281 TOKENS:')
seen=set()
for r in sorted(rows,key=lambda x:(x['tokens'],x['ast'],x['bytes'])):
 if r['tokens']>=281:break
 if r['sha256'] in seen:continue
 seen.add(r['sha256']);print(r)
