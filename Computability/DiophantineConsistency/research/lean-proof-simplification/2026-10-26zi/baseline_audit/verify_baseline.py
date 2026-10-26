#!/usr/bin/env python3
"""Verify supplied manifests against existing bytes. No network, extraction, writes or Lean."""
import argparse,hashlib,json
from pathlib import Path,PurePosixPath
R=Path(__file__).resolve().parent
def require(condition, message):
 if not condition:raise ValueError(message)
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);a=p.parse_args();root=a.repo.resolve()
 docs=json.loads((R/'DOCUMENT_SOURCES.json').read_text());ledger=json.loads((R/'ASSUMPTION_LEDGER.json').read_text());corpus=json.loads((R/'CORPUS_SUMMARY.json').read_text())
 require(len(ledger['ledger'])==168 and len({r['id'] for r in ledger['ledger']})==168, 'Ledger cardinality')
 cs={c['id'] for c in ledger['contracts']};require(len(cs)==25 and all(r['contract'] in cs for r in ledger['ledger']), 'Contract coverage')
 require(len(corpus['packets'])==21 and corpus['current_incoming_files']==['README.md'] and corpus['current_incoming_archives']==0, 'Corpus scope')
 require(corpus['placed_blob_count_inventoried']==sum(x['placed_blob_count'] for x in corpus['packets'])==1140, 'Placed inventory')
 require(corpus['placed_files_hash_bound']==894 and corpus['previous_manuscript_note_bindings']==45, 'Binding counts')
 require(len(docs)==corpus['document_and_technical_source_bindings']==279, 'Document coverage')
 seen=set();errors=[]
 for d in docs:
  rel=PurePosixPath(d['repository_path']);require(not rel.is_absolute() and '..' not in rel.parts and '\\' not in str(rel), 'Unsafe source path')
  key=str(rel);require(key not in seen, 'Duplicate source');seen.add(key);f=(root/key).resolve()
  if not f.is_relative_to(root):errors.append(key+': escapes root');continue
  try:b=f.read_bytes()
  except OSError as e:errors.append(key+': '+str(e));continue
  if len(b)!=d['size'] or blob(b)!=d['git_blob'] or hashlib.sha256(b).hexdigest()!=d['sha256']:errors.append(key+': hash/size mismatch')
 result={'status':'PASS' if not errors else 'FAIL','checked_documents_and_technical_sources':len(docs),'ledger_rows':168,'virtual_subsystems':25,'pin':ledger['pin'],'errors':errors,'scope':'Source byte/provenance checks only; no Lean invocation or new historical compile claim'}
 print(json.dumps(result,indent=2));return bool(errors)
if __name__=='__main__':raise SystemExit(main())
