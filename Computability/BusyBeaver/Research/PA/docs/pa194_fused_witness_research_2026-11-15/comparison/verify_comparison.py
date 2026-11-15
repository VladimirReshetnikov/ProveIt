#!/usr/bin/env python3
"""Replay the complete offline table comparison; no network or generators."""
from pathlib import Path
from collections import Counter
import argparse,csv,json
import canonical as C
ROOT=Path(__file__).resolve().parent

def require(test,why):
 if not test:raise ValueError(why)
def bisimulation(rows,states):
 block={q:0 for q in states}
 while True:
  signatures={q:tuple((w,d,block.get(n,-1))for b in(0,1)for w,d,n in[rows[q,b]])for q in states}
  ids={s:i for i,s in enumerate(sorted(set(signatures.values())))}
  new={q:ids[signatures[q]]for q in states}
  if len(set(new.values()))==len(set(block.values())):return len(ids)
  block=new

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=ROOT/'offline_verification.json');a=ap.parse_args()
 m=json.loads((ROOT/'manifest.json').read_text());summary=json.loads((ROOT/'summary.json').read_text())
 require(summary['pin']==m['pin'],'pin mismatch');require(not json.loads((ROOT/'missing.json').read_text()),'selected sources missing')
 with(ROOT/'source_bindings.csv').open()as f:bindings=list(csv.DictReader(f))
 require(len(bindings)==summary['tracked_selected_files']==13524,'source inventory count')
 exact=set();strong=set();states_count=Counter();bisim_count=Counter()
 for rec in m['spanning_tables']:
  p=ROOT/rec['path'];require(C.sha(p.read_bytes())==rec['sha256'],'changed representative bytes')
  rows,states=C.parse(p);require(len(states)==rec['states'],'wrong control count')
  k=C.key(rows,states);require(k==rec['exact_class'],'exact class mismatch')
  exact.add(k);states_count[len(states)]+=1
  if len(states)==194:
   sk=C.key(rows,states,True);require(sk==rec['strong_class'],'broad class mismatch');strong.add(sk)
   n=bisimulation(rows,states);require(n==rec['bisimulation_states'],'ordinary quotient mismatch');bisim_count[n]+=1
 require(states_count=={193:61,194:548},'wrong frontier corpus counts')
 require(bisim_count=={194:548},'ordinary quotient changed')
 disconnected_count=Counter()
 for rec in m['nonspanning_tables']:
  p=ROOT/rec['path'];require(C.sha(p.read_bytes())==rec['sha256'],'changed disconnected bytes')
  rows,states=C.parse(p);require(len(states)==rec['states']and C.key(rows,states)is None,'disconnected graph gained spanning root')
  disconnected_count[len(states)]+=1
 require(disconnected_count[194]==2,'diagnostic count')
 norm=json.loads((ROOT/'normalized_tables.json').read_text())
 with(ROOT/'named_designs104.csv').open()as f:named=list(csv.DictReader(f))
 for row in named:
  rec=norm[row['normalized_sha256']]
  require(rec['class']==row['canonical_class']and rec['states']==194,'named source binding')
 require(len(named)==len({r['canonical_class']for r in named})==104,'named classes not distinct')
 with(ROOT/'occurrences.csv').open()as f:occ=list(csv.DictReader(f))
 with(ROOT/'upstream_MACHINE_FILES.tsv').open()as f:old=list(csv.DictReader(f,delimiter='\t'))
 raw={r['source_sha256']for r in occ};coverage={}
 for ns in(193,194):
  classes={r['class']for r in old if int(r['states'])==ns}
  covered={r['class']for r in old if int(r['states'])==ns and r['sha256']in raw}
  require(classes==covered,'old catalogue representative missing');coverage[str(ns)]=len(covered)
 results=[]
 for rec in m['new_tables']:
  p=ROOT/rec['table'];require(C.sha(p.read_bytes())==rec['dense_sha256'],'changed new table')
  rows,states=C.parse(p);require(len(states)==194 and len(rows)==388,'new table count')
  require(0 in states and len(C.rooted(rows,states,0))==388,'start is not spanning')
  k=C.key(rows,states);sk=C.key(rows,states,True)
  require(k==rec['exact_class']and sk==rec['strong_class'],'new canonical identity changed')
  require(k not in exact and sk not in strong,'new table already in corpus')
  rename={q:101+7*q for q in states};halts={n for w,d,n in rows.values()}-states
  for h in halts:rename[h]=99999
  control={(rename[q],b^1):(w^1,'L'if d=='R'else'R',rename[n])for(q,b),(w,d,n)in rows.items()}
  control={a:((1,'L',n)if n==99999 else(w,d,n))for a,(w,d,n)in control.items()}
  require(C.key(control,{rename[q]for q in states},True)==sk,'symmetry positive control')
  results.append(dict(rec,positive_control=True,matches=[]))
 require(len(results)==len({r['strong_class']for r in results})==4,'new graphs repeat one another')
 report={'status':'PASS','pin':m['pin'],'selected_source_bindings':len(bindings),'missing_selected_blobs':0,'spanning_classes_by_states':dict(states_count),'nonspanning_literal_forms_by_states':dict(disconnected_count),'named_existing_classes':len(named),'ordinary_bisimulation_histogram194':dict(bisim_count),'old_catalogue_byte_coverage':coverage,'scope':m['scope'],'new_graphs':results,'proof_boundary':'This proves recorded table identity and structural novelty, not source correctness or absolute PA calibration. Those have separate source/physical proofs and certificates.'}
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
