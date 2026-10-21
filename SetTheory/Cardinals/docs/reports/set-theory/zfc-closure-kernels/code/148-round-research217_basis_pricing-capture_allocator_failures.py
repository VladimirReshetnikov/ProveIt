"""Owned capture of already-tested allocator outputs before failed binding checks."""
import price_h_pw as B
import json,time
P=B.P;original=P.allocation;cached=original(B.T,B.old);captured={}
def probe(table,tree):
 if table is B.T and tree is B.old:return cached
 captured['table']=table.copy();captured['tree']=tree
 return original(table,tree)
reports=[];start=time.monotonic();P.allocation=probe
try:
 for r in json.load(open(B.OUT/'PARSER_PRESERVING_PRICES.json'))['results']:
  if time.monotonic()-start>5:break
  captured.clear();new=P.tree(json.load(open(B.OUT/r['source_file'])))
  try:out,receipt=P.compile(B.T,B.old,new);error=None
  except Exception as e:error=repr(e)
  out=captured.get('table');rec=dict(index=r['index'],source_sha256=r['source_sha256'],binding_error=error,status='INVALID_PROVISIONAL_ALLOCATION_NOT_A_MACHINE_CONSTRUCTION')
  if out is not None:
   raw=P.M.enc(out);name=f"h_pw_{r['index']:02d}.invalid_allocator.native.tm";(B.OUT/name).write_bytes(raw)
   changes=[dict(row=list(row),old=list(B.T[row])if row in B.T else None,new=list(a))for row,a in sorted(out.items())if B.T.get(row)!=a]
   rec.update(raw_allocated_states=len(out)//2,raw_rows=len(out),file=name,sha256=B.H(raw),changes=changes,warning='Literal failed allocator output. State count is only the size of an invalid table; no source implementation, runtime, or halting equivalence is claimed.')
  reports.append(rec)
finally:P.allocation=original
B.dump('FAILED_ALLOCATOR_OUTPUTS.json',dict(status='COMPLETE'if len(reports)==12 else'CAP_UNKNOWN',reports=reports,seconds=time.monotonic()-start,scope='Diagnostic capture of the same12 approved cases, not another search.'))
print('counts',[(r['index'],r.get('raw_allocated_states'))for r in reports],'seconds',time.monotonic()-start)
