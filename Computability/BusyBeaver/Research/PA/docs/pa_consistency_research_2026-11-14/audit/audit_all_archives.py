#!/usr/bin/env python3
"""Unbounded-depth, SHA-256 deduplicated PA archive inventory.

All archive bodies are traversed once; every encountered archive reference is
recorded. This avoids giving repeated nested copies extra design identities.
Numeric-table graph classification reuses the independent exact parser and
canonicalizer in audit_archives.py. Start choices remain a separate question.
"""
from pathlib import Path
from collections import Counter
import argparse,hashlib,io,json,re,zipfile,subprocess
from audit_archives import sha,parse_tm,canonical,TEXT

HERE=Path(__file__).resolve().parent

def main():
 ap=argparse.ArgumentParser()
 ap.add_argument('--repo',type=Path,required=True,help='ProveIt checkout at the pinned source commit')
 ap.add_argument('--output',type=Path,default=HERE/'all_depths')
 ap.add_argument('--cache',type=Path,help='Earlier exact table-classification cache')
 args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
 expected_commit='906367250a7f96c923147b10df392294bced7be5'
 actual_commit=subprocess.check_output(['git','-C',str(args.repo),'rev-parse','HEAD'],text=True).strip()
 if actual_commit!=expected_commit:raise ValueError('Check out the pinned source commit before replaying this inventory')
 cache={}
 if args.cache:
  for t in json.loads(args.cache.read_text())['tables']:
   cache[t['sha256']]={k:v for k,v in t.items()if k not in ('archive','path','sha256')}
 members=[];tables=[];archives=[];references=[];excerpts=[];seen={};seen_text=set();top=[]
 def inspect(archive,name,data,depth):
  digest=sha(data);p=Path(name)
  members.append({'archive':archive,'path':name,'size':len(data),'sha256':digest})
  if p.suffix.lower()=='.zip':walk(archive,name,data,depth);return
  if p.suffix.lower()not in TEXT or len(data)>2_000_000:return
  if digest not in cache:
   parsed=parse_tm(data)
   if parsed:
    rows,states,halts,start=parsed;key,nroots=canonical(rows,states)
    cache[digest]={'working_states':len(states),'rows':len(rows),'halt_labels':sorted(halts),
      'declared_start':start,'root_free_isomorphism_sha256':key,'roots_reaching_all_states':nroots}
   else:cache[digest]=None
  if cache[digest]:tables.append({'archive':archive,'path':name,'sha256':digest,**cache[digest]})
  if digest in seen_text:return
  seen_text.add(digest)
  if p.suffix.lower()in {'.tex','.md','.txt'}and any(k in name.lower()for k in ('readme','report','comparison','summary')):
   try:text=data.decode()
   except UnicodeDecodeError:return
   paras=re.split(r'\n\s*\n',text)
   selected=[p for p in paras if re.search(r'\b(?:19\d|2\d\d)\b|state|distinct|equivalen|rejected|verified|kernel|interpret',p,re.I)]
   if selected:excerpts.append({'archive':archive,'path':name,'sha256':digest,'paragraphs':selected[:80]})
 def walk(archive,name,data,depth):
  digest=sha(data);rep=seen.get(digest)
  references.append({'archive':archive,'path':name,'sha256':digest,'depth':depth,'first_visit':rep is None})
  if rep is not None:return
  seen[digest]=(archive,name)
  with zipfile.ZipFile(io.BytesIO(data))as z:
   infos=[i for i in z.infolist()if not i.is_dir()]
   archives.append({'sha256':digest,'representative_archive':archive,'representative_path':name,'depth':depth,
    'zip_bytes':len(data),'members':len(infos),'uncompressed_bytes':sum(i.file_size for i in infos)})
   print('archive',len(archives),'depth',depth,'members',len(infos),name.rsplit('!/',1)[-1],flush=True)
   for info in infos:
    if info.file_size>200_000_000:raise ValueError('Unexpected oversized member: '+name+'!/'+info.filename)
    inspect(archive,(name+'!/'if name else'')+info.filename,z.read(info),depth+1)
 for path in sorted((args.repo/'docs/incoming').glob('*.zip')):
  data=path.read_bytes();top.append({'name':path.name,'sha256':sha(data),'zip_bytes':len(data)})
  walk(path.name,'',data,0)
 pa=args.repo/'Computability/BusyBeaver/Research/PA'
 for path in sorted(pa.rglob('*')):
  if path.is_file()and path.suffix.lower()in TEXT|{'.zip'}:
   inspect('PA-directory',str(path.relative_to(args.repo)),path.read_bytes(),0)
 groups={}
 for t in tables:groups.setdefault((t['working_states'],t['root_free_isomorphism_sha256']),[]).append(t)
 census=Counter(t['working_states']for t in {t['sha256']:t for t in tables}.values())
 group_counts=Counter(k[0]for k in groups)
 summary={'top_level_archives':len(top),'unique_archive_bodies':len(archives),'archive_references':len(references),
  'maximum_encountered_depth':max(x['depth']for x in references),'file_occurrences_in_unique_archives_and_PA':len(members),
  'table_occurrences':len(tables),'distinct_table_byte_forms':len({t['sha256']for t in tables}),
  'root_free_graph_classes':len(groups),'size_families':[{ 'working_states':n,'distinct_byte_forms':census[n],
     'root_free_graph_classes':group_counts[n]}for n in sorted(census)],
  'classification_warning':'Includes rejected, experimental, intermediate and synthetic tables; counts do not assert accepted consistency machines.'}
 payload={'source_commit':'906367250a7f96c923147b10df392294bced7be5','scope':'All nesting depths, archive bodies deduplicated by SHA-256',
  'top_level_archives':top,'archives':archives,'archive_references':references,'members':members,'tables':tables,'summary':summary,
  'table_identity_caveat':'Root-free graph identity ignores the start state; accepted status and logical correctness must be assessed separately.'}
 (args.output/'inventory.json').write_text(json.dumps(payload,indent=2)+'\n')
 (args.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
 (args.output/'excerpts.json').write_text(json.dumps(excerpts,indent=2)+'\n')
 (args.output/'table_groups.json').write_text(json.dumps([{'working_states':k[0],'canonical_sha256':k[1],
  'occurrences':len(v),'distinct_byte_forms':len({x['sha256']for x in v}),'members':v}for k,v in sorted(groups.items(),key=lambda x:(x[0][0],str(x[0][1])))],indent=2)+'\n')
 print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
