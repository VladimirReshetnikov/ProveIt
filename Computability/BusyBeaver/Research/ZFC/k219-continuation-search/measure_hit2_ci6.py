#!/usr/bin/env python3
"""Measure the literal hit2 equality source on both preserved K219 allocators.
Only exact source/decoder-prefix binding is checked. No runtime certificate.
"""
from pathlib import Path
import argparse,hashlib,importlib,json,sys,time
P=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 need(__debug__ and not sys.flags.optimize,'Assertions must be enabled');need(not a.output.exists(),'Output must be fresh')
 source=P/'../k219-source-search/candidates/hit02.sites.json';baseline=P/'../candidate-k219'
 pins={str(source.resolve()):'f5c9a64cd571cb764bb00fff84f519df75f4381df3ec0ce51eced6d29ec28b64',str((baseline/'sites219.json').resolve()):'0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789',str((baseline/'k219.native.tm').resolve()):'b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'}
 for name,d in json.loads((P/'compiler-inputs/ci6-provenance.json').read_text()).items():pins[str((P/'compiler-inputs'/name).resolve())]=d['sha256']
 need(all(sha(Path(p))==h for p,h in pins.items()),'Pinned input drift')
 sys.dont_write_bytecode=True;sys.path.insert(0,str((P/'compiler-inputs').resolve()))
 s=importlib.import_module('source_language');b=importlib.import_module('build221');original=importlib.import_module('measure_ci6_hypothesis');protected=importlib.import_module('measure_protected_ci6_hypothesis')
 old=s.tree(json.loads((baseline/'sites219.json').read_text()));rows=json.loads(source.read_text());new=s.tree(rows);table=b.read_table((baseline/'k219.native.tm').read_bytes())
 need(s.graph_arithmetic(rows)[0]==s.graph_intervals(rows),'Independent new-source CFG disagreement')
 need(s.metrics(new)['dag_nodes']==207 and len(rows)==4744,'Expected exact hit2 census')
 need(not any(path[-1]=='1' and op=='CD' for path,op,arg in rows),'Unexpected right-child decrement')
 a.output.mkdir(parents=True);(a.output/'sites.json').write_bytes(source.read_bytes());(a.output/'measure_hit2.py').write_bytes(Path(__file__).read_bytes())
 results=[]
 for name,module in [('origin_reuse',original),('protected',protected)]:
  started=time.monotonic();identity,im=module.compile_tree(s,b,table,old,old)
  need(identity==table and im['working_states']==219,'Identity compiler control')
  row={'policy':name,'identity_control':im,'status':'PENDING'}
  try:
   compiled,metrics=module.compile_tree(s,b,table,old,new)
   raw=b.table_bytes(compiled);need(b.read_table(raw)==compiled,'Raw table roundtrip')
   (a.output/(name+'.native.tm')).write_bytes(raw)
   row.update(status='DECODER_BINDING_PASS_WITH_UNVERIFIED_CI6_RIGHT_ENTRY',metrics=metrics,raw_sha256=hashlib.sha256(raw).hexdigest(),helper302_retained=302 in {q for q,bit in compiled})
  except (ValueError,KeyError,AssertionError) as exc:
   row.update(status='COMPILER_REJECTED',error=repr(exc))
  row['seconds']=time.monotonic()-started;results.append(row);dump(a.output/(name+'.json'),row)
 need(all(sha(Path(p))==h for p,h in pins.items()),'Input drift after measurement')
 result={'status':'BOUNDED_HIT2_COMPILER_MEASUREMENT_COMPLETE','inputs':pins,'source_metrics':s.metrics(new),'right_child_decrements':0,'policies':results,'source_proof':'Separate all-natural equality-macro proof in k219-source-search; not established by this measurement.','unverified_entry':{'opcode':'CI6','branch':1,'action':[1,1,13],'basis':'Symmetric generic left-CI6 entry; no right-context runtime proof yet.'},'scope':'Raw allocation count and exact decoder-prefix binding only. No primitive runtime/startup replay, no calibrated new machine, no Lean/Rocq endpoint.'}
 dump(a.output/'result.json',result);print(json.dumps(result,indent=2))
if __name__=='__main__':main()
