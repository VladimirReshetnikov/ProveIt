#!/usr/bin/env python3
"""Authenticate coherent big-endian specialization and replay complete Pc1."""
from pathlib import Path
import argparse,gzip,hashlib,importlib.util,json,subprocess,sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent))

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def run():
    checker=module('independent_inverse_trace_checker',ROOT.parent/'verify.py');checker.ROOT=ROOT
    pins=checker.check_source_pins()
    path=ROOT/'equation_bV.json';g=json.loads(path.read_text())
    parent_path=ROOT/g['parent']['path'];parent=json.loads(parent_path.read_text())
    checker.require(hashlib.sha256(parent_path.read_bytes()).hexdigest()==g['parent']['sha256'],'free-port graph pin')
    checker.require(g['source']==parent['source'],'free-port graph identity')
    native=json.loads((ROOT/'snapshot/candidates/one-page-one-anchor7309/polynomial.json').read_text())
    checker.require(g['coefficient_binding']['ports']==native['coefficient_binding']['ports'],'whole coherent tuple identity')
    command=[sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])+[str(ROOT/'snapshot/research/one-anchor-independent/certify.py')]
    run=subprocess.run(command,check=True,capture_output=True,text=True)
    checker.require(not run.stderr,'Pc1 stderr')
    pc1=json.loads(run.stdout);checker.require(pc1['status']=='PASS','Pc1 status')
    rebuild=module('pinned_exact_one_anchor7309_reconstruction',ROOT/'snapshot/research/one-anchor-independent/certify.py')
    _,seed,actions,tiles,c,support=rebuild.model();values,_=rebuild.constants(c,support)
    for port,key in [('beta','beta'),('K0','K'),('MC','MC'),('MF','MF_source')]:
        item=g['coefficient_binding']['ports'][port]
        raw=gzip.decompress((ROOT/'coefficients'/item['file']).read_bytes())
        checker.require(int.from_bytes(raw,'big')==values[key],'reconstructed entire port '+port)
        checker.require(len(raw)==(values[key].bit_length()+7)//8,'minimal unsigned encoding')
    raw_bytes=sum((v.bit_length()+7)//8 for v in values.values())
    checker.require(raw_bytes==172011,'whole tuple bytes')
    return {'source_pins':pins,'Pc1':pc1,'raw_bytes':raw_bytes,'largest_port_bits':max(v.bit_length() for v in values.values()),'seed_characters':len(seed),'actions':len(actions),'tiles':len(tiles),'operations':g['operations'],'operation_breakdown':checker.topology(g),'exact_cuts':checker.exact_cuts(g),'leading':checker.leading(g),'coefficients':checker.coefficients(g),'rejected_mutations':checker.mutations(g),'scope':'Whole tuple substitution at separately authenticated native calibration; not merely a port-box inference.'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);a=ap.parse_args();r=run()
    if a.receipt:a.receipt.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:r[k] for k in ('source_pins','Pc1','raw_bytes','largest_port_bits','operations','rejected_mutations')},indent=2))
if __name__=='__main__':main()
