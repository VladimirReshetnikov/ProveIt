if not __debug__: raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
"""Portable freshly-authored regeneration of the frozen nine-variable candidate.
Run from any directory with --compiler-root pointing to the delivered compact
compiler folder. No received upstream program is imported or executed.
"""
import argparse,hashlib,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'review'))
from generic_jones_circuit import construct as base_construct
from optimize_nine_circuit import audit_body
from prepare_coefficients import prepare
from build_compact_nine import construct,index_bound

def main():
 p=argparse.ArgumentParser();p.add_argument('--parent',type=Path,default=HERE.parent/'arithmetic/quartic31.json');p.add_argument('--compiler-root',type=Path,required=True);p.add_argument('--output',type=Path,default=HERE/'rebuilt_nu31');args=p.parse_args()
 data=args.parent.read_bytes();parent=json.loads(data);c,q=prepare(parent);c['parent_sha256']=hashlib.sha256(data).hexdigest();c['parent_file']=args.parent.name
 manifest=json.loads((args.compiler_root/'COMPACT_COEFFICIENT_BINDING.json').read_text());c,bound=index_bound(c,manifest);c['port_binding']='AUTHORITATIVE FINAL BINDING: the complete compact943 tuple in COMPACT_COEFFICIENT_BINDING.json overrides the historical default t-shape metadata in the inert parent source. beta=beta, K0=K, MC=MC, MF=MF_source.';c['nu_caution']='nu=31 counts the witnesses in the new normalized quartic. Compact radix exponent 5^10 does not justify nu=9.'
 base=base_construct(c);new=construct(base,1,True);new['source_circuit']='nine_generic31_majorant.json';new['index_exponent']=c['index_exponent']
 assert c['nu']==31 and c['index_exponent']==45933757
 assert len(c['coefficient_records'])==402 and audit_body(new)['live_operations']==1840
 args.output.mkdir(parents=True,exist_ok=True)
 for name,obj in [('COMPACT_CONSTANTS.json',c),('INDEX_BOUND_CERTIFICATE.json',bound),('shifted_quartic.json',q),('nine_generic31_majorant.json',base),('nine_compact_magnitude_tight.json',new)]:
  (args.output/name).write_text(json.dumps(obj,separators=(',',':'))+'\n')
 frozen=json.loads((HERE/'nu31/nine_compact_magnitude_tight.json').read_text());assert new==frozen,'Regenerated arithmetic circuit differs from frozen candidate'
 print(json.dumps(dict(status='PASS',full_frozen_circuit_equality=True,circuit=audit_body(new),nu=c['nu'],index_exponent=c['index_exponent']),indent=2))
if __name__=='__main__':main()
