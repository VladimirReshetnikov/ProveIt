#!/usr/bin/env python3
"""Reproducible literal-table census; no correctness claim follows from inclusion.
Accepts five-column complete binary tables from .tm or .txt ZIP members.
All nested ZIP occurrences are visited; explicit graph starts are not guessed.
"""
import argparse, hashlib, io, json, re, zipfile
from collections import Counter
from pathlib import Path

PIN='5be8b9236df6a6d308195e62a906a173dc70d00a'
ROW=re.compile(r'^\s*(\d+)\s+([01])\s+([01])\s+([LR])\s+(\d+)\s*(?:#.*)?$')

def sha(b): return hashlib.sha256(b).hexdigest()
def parse(b):
 try: s=b.decode('utf-8-sig')
 except UnicodeError: return None
 rows={}
 for ln in s.splitlines():
  if not ln.strip() or ln.lstrip().startswith(('#','//','%',';')): continue
  m=ROW.match(ln)
  if m is None:return None
  q,r,w,d,n=m.groups(); q,r,w,n=map(int,(q,r,w,n))
  if (q,r) in rows: return None
  rows[q,r]=(w,d,n)
 if not rows:return None
 states={q for q,r in rows}
 if set(rows)!={(q,r) for q in states for r in (0,1)}: return None
 extra={n for w,d,n in rows.values()}-states
 if len(extra)>1: return None
 normalized='\n'.join(f'{q} {r} {w} {d} {n}' for (q,r),(w,d,n) in sorted(rows.items()))+'\n'
 return {'states':len(states),'rows':len(rows),'terminal_labels':sorted(extra),'raw_sha256':sha(b),'labeled_function_sha256':sha(normalized.encode())}

def main():
 a=argparse.ArgumentParser();a.add_argument('--manifest',type=Path,default=Path(__file__).parent/'corpus/source_manifest.json');a.add_argument('--archive-dir',type=Path,required=True);a.add_argument('--out',type=Path,required=True);a.add_argument('--pa',type=Path);args=a.parse_args()
 inp=json.loads(args.manifest.read_text());tables=[];archives=[];zip_occurrences=[];errors=[]
 def inspect(raw,loc,outer,depth):
  zip_occurrences.append({'member':loc,'sha256':sha(raw),'bytes':len(raw),'depth':depth})
  with zipfile.ZipFile(io.BytesIO(raw)) as z:
   members=0
   for zi in z.infolist():
    if zi.is_dir():continue
    members+=1;n=zi.filename;where=loc+'!'+n
    if n.lower().endswith('.zip'):
     try: inspect(z.read(zi),where,outer,depth+1)
     except (zipfile.BadZipFile,RuntimeError,OSError) as e: errors.append({'member':where,'error':str(e)})
    elif n.lower().endswith(('.tm','.txt')):
     p=parse(z.read(zi))
     if p is not None: tables.append(dict(outer_archive=outer,member=where,depth=depth,**p))
   return members
 for item in inp:
  if not item['name'].endswith('.zip'):continue
  p=args.archive_dir/item['name']; b=p.read_bytes(); actual=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  if actual!=item['git_blob']: raise ValueError((p,'Git blob mismatch'))
  before=len(tables);m=inspect(b,item['name'],item['name'],0)
  a={k:v for k,v in item.items() if k!='path'};a.update(bytes=len(b),outer_file_members=m,recursive_recognized_tables=len(tables)-before);archives.append(a)
  print(item['name'],len(tables)-before,flush=True)
 if args.pa:
  for p in sorted(args.pa.rglob('*.tm')):
   parsed=parse(p.read_bytes())
   if parsed:tables.append(dict(outer_archive=None,member=str(p.relative_to(args.pa)),depth=None,**parsed))
 counts=Counter(t['states'] for t in tables)
 result={'pin':PIN,'definition':'Complete numeric five-column binary .tm/.txt tables; all nested ZIP occurrences; direct PA .tm files; no inferred start and no correctness inference','archives':archives,'zip_occurrences':zip_occurrences,'tables':tables,'errors':errors,'summary':{'top_level_zip_count':len(archives),'zip_occurrences':len(zip_occurrences),'unique_zip_payloads':len({z['sha256'] for z in zip_occurrences}),'total_zip_bytes':sum(a['bytes'] for a in archives),'literal_table_occurrences':len(tables),'unique_raw_tables':len({t['raw_sha256'] for t in tables}),'unique_labeled_functions':len({t['labeled_function_sha256'] for t in tables}),'by_working_state_count':dict(sorted(counts.items()))}}
 args.out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result['summary'],indent=2))
if __name__=='__main__':main()
