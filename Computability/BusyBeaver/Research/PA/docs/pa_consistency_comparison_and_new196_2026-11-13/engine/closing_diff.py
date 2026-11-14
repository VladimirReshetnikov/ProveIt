#!/usr/bin/env python3
"""Certify which base primitive cases can meet a changed closing dispatch row.
The unchanged cases execute identically in each variant. The refined collector
rechecks the affected cases and unions them with the base context enclosure.
"""
from pathlib import Path
import hashlib,importlib.util,json,sys
BASE=Path(__file__).resolve().parent

def load(path,name):
 sp=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);return m

def table(directory):
 labels=json.loads((directory/'labels.json').read_text());rows={}
 for ln in(directory/'machine.tm').read_text().splitlines():
  q,b,w,d,t=ln.split();rows[labels[int(q)],int(b)]=(int(w),d=='R',labels[int(t)])
 return rows,labels

def verify():
 base=BASE/'trit_diagonal196';rows,labels=table(base);fast=load(BASE/'fast_contexts.py','diff_fast');s=load(BASE/'inputs/native_symbolic_runtime.py','diff_runtime');raw=json.loads((base/'sites.json').read_text());s.program=lambda:fast.program(raw)
 changed=set();variants={}
 for r in range(3,7):
  path=BASE/f'trit_diagonal_close{r}';new,ll=table(path);assert labels==ll and rows.keys()==new.keys()
  keys=[key for key in rows if rows[key]!=new[key]];assert keys==[(2067,1)],keys
  changed.update(q for q,b in keys);sites=json.loads((path/'sites.json').read_text());assert [i for i in range(len(raw))if raw[i]!=sites[i]]==[3580]
  variants[str(r)]={'changed_rows':[[list(k),list(rows[k]),list(new[k])]for k in keys],'changed_source_sites':[3580],'source_sha256':hashlib.sha256((path/'sites.json').read_bytes()).hexdigest(),'labels_sha256':hashlib.sha256((path/'labels.json').read_bytes()).hexdigest(),'machine_sha256':hashlib.sha256((path/'machine.tm').read_bytes()).hexdigest()}
 selected=set();branches=0
 for ct in s.contracts():
  visited=set();steps=s.run(rows,ct,observe=lambda state:visited.add(state[0]));assert steps is not None
  if visited&changed:selected.add(ct[0]);branches+=1
 receipt={'base_machine_sha256':hashlib.sha256((base/'machine.tm').read_bytes()).hexdigest(),'base_source_sha256':hashlib.sha256((base/'sites.json').read_bytes()).hexdigest(),'base_context_sha256':hashlib.sha256((base/'trit_ones_contexts/source_contexts.txt').read_bytes()).hexdigest(),'contracts_checked':4815,'affected_source_sites':sorted(selected),'affected_branches':branches,'changed_states_outside_boxed_engine':all(q not in s.BOXSTATES for q in changed),'variants':variants,'scope':'Every base primitive contract not selected executes identically because it never visits a modified control. Selected cases and exact startup must be rechecked on each variant. The base local enclosure is retained, so obsolete contexts cause conservative rejection only.'}
 return receipt

def main():
 receipt=verify();base=BASE/'trit_diagonal196'
 (base/'closing_differential_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
