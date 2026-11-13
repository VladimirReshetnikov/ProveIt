from pathlib import Path
import argparse, ast, csv, gzip, hashlib, io, json, tokenize, zipfile

parser=argparse.ArgumentParser(description='Read-only census of the pinned ConciseIPRA Python sources.')
parser.add_argument('repository', type=Path, help='Local ProveIt repository root')
parser.add_argument('--output', type=Path, default=Path('census_output'))
args=parser.parse_args()
BASE=args.repository/'Logic/PrimitiveRecursiveArithmetic/ConciseIPRA'
rows=[]; cache={}; failures=[]
def source(name,data,location):
    if name.endswith('.py.gz'):
        try:data=gzip.decompress(data)
        except Exception:return
    digest=hashlib.sha256(data).hexdigest()
    if digest not in cache:
        try:
            text=data.decode('utf-8-sig'); tree=ast.parse(text)
            normalized=ast.unparse(tree)+'\n'
            ignore={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NL,tokenize.NEWLINE,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT}
            significant=sum(t.type not in ignore for t in tokenize.generate_tokens(io.StringIO(normalized).readline))
            metric={'tokens':significant,'ast_nodes':sum(1 for _ in ast.walk(tree)),'normalized_bytes':len(normalized.encode()),'source_bytes':len(data),'accept':"ACCEPT" in text,'json':any(x in text for x in ('json','load(','loads(')),'packed':any(x in text for x in ('exec(', 'eval(', '__import__','decompress('))}
            cache[digest]=metric
        except Exception as ex: failures.append({'path':name,'error':str(ex)});return
    rows.append({'path':name,'location':location,'sha256':digest,**cache[digest]})
def archive(name,data,depth=0):
    if depth>5:raise ValueError('Nested archive depth exceeds audited bound: '+name)
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        for item in z.infolist():
            path=name+'::'+item.filename
            if item.filename.endswith(('.py','.py.gz')):source(path,z.read(item),'archive')
            elif item.filename.endswith('.zip'):archive(path,z.read(item),depth+1)
for path in sorted((BASE/'Artifacts').rglob('*')):
    if path.is_file() and path.name.endswith(('.py','.py.gz')):source(str(path.relative_to(BASE)),path.read_bytes(),'artifact')
for path in sorted((BASE/'docs/incoming').glob('*.zip')):archive(str(path.relative_to(BASE)),path.read_bytes())
dest=args.output
dest.mkdir(parents=True,exist_ok=True)
with (dest/'frontier_census.csv').open('w') as f:
    writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
(dest/'frontier_census.json').write_text(json.dumps({'python':__import__('sys').version,'snapshot':'78edba03ee060644464f76e388578584b356520a','rows':rows,'parse_failures':failures},indent=2)+'\n')
unique={r['sha256']:r for r in rows if r['accept'] and r['json'] and not r['packed'] and not any(x in r['path'].lower() for x in ('unsound','negative/','rejected_','no_parity','illustration'))}
print(json.dumps({'instances':len(rows),'unique_sources':len(cache),'parse_failures':len(failures),'shortlists':{k:sorted(unique.values(),key=lambda x:x[k])[:15] for k in ('tokens','ast_nodes','normalized_bytes')}},indent=2))
