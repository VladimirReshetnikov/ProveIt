"""Instantiate all Jones fixed leaves coherently at a new complete compiler tuple.

Run after optimize_combined.py. The astronomical y integer is specified by a
bounded finite sum, never treated as an unknown and never materialized.
"""
from pathlib import Path
from collections import defaultdict
import argparse, gzip, hashlib, json
from circuit_tools import audit_body

if not __debug__:
    raise SystemExit('Run without -O: assertions are exact audit checks.')

HERE=Path(__file__).resolve().parent

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--coefficients',type=Path,default=HERE.parent/'coefficients')
    args=parser.parse_args();root=args.coefficients.resolve()
    bind=json.loads((root/'COEFFICIENT_BINDING.json').read_text())
    manifests=bind['materialization']['files'];bitlengths={};hashes={}
    for row in manifests:
        payload=gzip.decompress((root/row['file']).read_bytes())
        assert hashlib.sha256(payload).hexdigest()==row['sha256']
        value=int.from_bytes(payload,'little')
        assert value.bit_length()==row['bits']
        bitlengths[row['port']]=row['bits'];hashes[row['port']]=row['sha256']
    bits=[bitlengths[k] for k in ('beta','K','MC','MF_source')]
    constants=json.loads((HERE/'source/COMPACT_CONSTANTS.json').read_text())
    certificate=[];smax=0
    for row in constants['coefficient_records']:
        terms=defaultdict(int)
        for term in row['coefficient_polynomial_in_fixed_ports']:
            terms[sum(x*y for x,y in zip(bits,term['powers']))]+=abs(term['coefficient'])
        h=sum(c<<e for e,c in terms.items());s=(h+1).bit_length()
        assert h+1<(1<<s)
        smax=max(smax,s)
        certificate.append({'name':row['name'],'power_of_two_terms':[{'exponent':e,'multiplier':c} for e,c in sorted(terms.items())],'minimal_power_for_this_bound':s})
    constants.update(port_binding='../coefficients/COEFFICIENT_BINDING.json; all four ports are mandatory, K0=K and MF=MF_source.',z_index=f'2^{smax}',index_exponent=smax,actual_port_bit_lengths=bits,parent_file='source/quartic31.json',index_bound_proof='For every weighted coefficient c_alpha, |c_alpha| <= H_alpha = sum |term coefficient|*2^(dot(port powers,port bit lengths)); the exact sparse-integer check proves H_alpha+1 < 2^index_exponent.',previous_index_bound='Original package30 exponent 45933757; this file rebinds every fixed coefficient at the new complete tuple.',nu_caution='nu=31 counts parent witness variables and is unrelated to native compiler radix d.')
    constants['port_binding']='../../coefficients/COEFFICIENT_BINDING.json; all four ports are mandatory, K0=K and MF=MF_source.'
    constants['parent_file']='../source/quartic31.json'
    constants['coherent_binding']={'instance':bind['instance'],'binding_file':'../../coefficients/COEFFICIENT_BINDING.json','port_sha256':hashes,'source_pin':bind['source_commit'],'all_unlisted_weighted_coefficients':0,'coefficient_aliases':'../coefficient_aliases.json'}
    # Explicit y includes every alpha of total degree <=4, not only nonzero corrections.
    constants['y_index']={'definition':'sum_{alpha in N^32, |alpha|<=4} (z_index+c_alpha)*(2*z_index)^(5^32-sum_j alpha_j*5^j)','bounded_sum_cardinality':58905,'zero_record_rule':'c_alpha=0 for every alpha absent from coefficient_records','status':'bounded exact integer recipe; not an unknown; not materialized'}
    constants['u_index_unused_by_body']='sum_{j=1}^{31}(2*z_index)^(5^j)'
    out=HERE/'compact';out.mkdir(exist_ok=True)
    (out/'CONSTANTS.json').write_text(json.dumps(constants,indent=2)+'\n')
    (out/'INDEX_BOUND_CERTIFICATE.json').write_text(json.dumps({'status':'PASS','index_exponent':smax,'port_bit_lengths':bits,'records':certificate},indent=2)+'\n')
    z=1<<smax;raw=z.to_bytes((z.bit_length()+7)//8,'little');gz=gzip.compress(raw,mtime=0)
    (out/'z_index.bin.gz').write_bytes(gz)
    receipts={}
    for domain in ('natural','positive'):
        body=json.loads((HERE/f'nine31_folded_{domain}.json').read_text())
        body['source_polynomial']='Same structural nu31 Jones equation, coherently rebound to '+bind['instance']
        body['coefficient_binding']={'constants':'CONSTANTS.json','ports':'../../coefficients/COEFFICIENT_BINDING.json','aliases':'../coefficient_aliases.json','z_materialized':'z_index.bin.gz','y':'bounded finite sum in CONSTANTS.json','warning':'All leaves are fixed integers defined by these recipes, not additional unknowns.'}
        body['index_exponent']=smax
        body['exact_degree']=120724*5**32+366
        body['diagonal_leading_coefficient_recipe']='2^274*z_index^2'
        (out/f'nine31_{domain}.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
        receipts[domain]=audit_body(body)
    receipts.update(status='PASS',nu=31,exact_degree=120724*5**32+366,index_exponent=smax,port_bit_lengths=bits,z_index={'recipe':f'2^{smax}','byte_order':'little','raw_bytes':len(raw),'gzip_bytes':len(gz),'sha256':hashlib.sha256(raw).hexdigest()},fixed_integer_status='The 402 weighted coefficient records define 78 nonliteral circuit leaves plus z and y; every absent weighted coefficient is zero. The fixed y is an exact 58905-term recipe.',proof_dependency='The new complete compiler tuple must satisfy the same quartic31 native compiler interface. Its independent geometry and padding proof is in ../coefficients/. No fresh proof-assistant endpoint is claimed.')
    (out/'REBOUND_CHECKS.json').write_text(json.dumps(receipts,indent=2)+'\n')
    print(json.dumps(receipts,indent=2))

if __name__=='__main__':main()
