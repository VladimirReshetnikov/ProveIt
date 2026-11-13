import hashlib,io,json,pathlib,re,zipfile
root=pathlib.Path('ProveIt/docs/drafts'); out=pathlib.Path('audit_work/text_corpus');out.mkdir(exist_ok=True)
seen_zip=set(); docs={}
def walk(raw,prefix):
 h=hashlib.sha256(raw).hexdigest()
 if h in seen_zip:return
 seen_zip.add(h)
 with zipfile.ZipFile(io.BytesIO(raw)) as z:
  for n in z.namelist():
   if n.endswith('/'):continue
   ext=pathlib.PurePosixPath(n).suffix.lower()
   if ext=='.zip':walk(z.read(n),prefix+'!/'+n)
   elif ext in {'.tex','.md','.txt','.rst'}:
    b=z.read(n);d=hashlib.sha256(b).hexdigest()
    docs.setdefault(d,{'sources':[],'bytes':len(b)})['sources'].append(prefix+'!/'+n)
    (out/(d+'.txt')).write_bytes(b)
for p in sorted(root.glob('*.zip')):walk(p.read_bytes(),p.name)
(out/'manifest.json').write_text(json.dumps({'archives':len(seen_zip),'documents':docs},indent=2))
print(len(seen_zip),len(docs))
queries={
 'sequence':r'eventual|cofinite|finite.support|finite.perturb|finite.range.sequence|constant.sequence|coordinate.permut|coordinate.swap',
 'progress_binder':r'progressive.binder|\bHI\b|\bHE\b|true.positions|integer.half|half.function|\\mathsf\{H\}|\\mathsf H|\\mathsf\{Step\}|universal.{0,35}progress|progress.{0,35}universal|parity|half\(',
 'product_coverage':r'product|\\times|coordinatewise'
}
ans={}
for k,pat in queries.items():
 hits=[]
 for h,meta in docs.items():
  text=(out/(h+'.txt')).read_text(errors='replace');lines=text.splitlines()
  if k=='product_coverage' and 'coverage' not in text.lower():continue
  mm=[{'line':i+1,'text':'\n'.join(lines[max(0,i-1):i+2])} for i,l in enumerate(lines) if re.search(pat,l,re.I)]
  if mm:hits.append({'hash':h,'source':meta['sources'][0],'matches':mm})
 ans[k]=hits
(pathlib.Path('audit_work')/'novelty_scan_detailed.json').write_text(json.dumps(ans,indent=2))
for k,hits in ans.items():
 print('\nQUERY',k,'docs',len(hits))
 if k=='sequence':
  for h in hits:
   print(h['source'])
   for m in h['matches']:print(m['line'],m['text'])
