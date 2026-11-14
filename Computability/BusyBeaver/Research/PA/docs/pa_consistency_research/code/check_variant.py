#!/usr/bin/env python3
"""Finite identity checks for the newly constructed 196-state variant.
Run check_runtime.py and check_startup.py separately for the execution proofs.
"""
import json
from verify import ROOT,require,digest,table,canonical,from_rows,statistics,graph_by_intervals,graph_by_bits

def main():
 native=ROOT/'data/variant196.native.tm';dense=ROOT/'data/variant196.tm'
 require(digest(native)=='f6594edc95efed02f26b88f71c9b1f7699965a258739836f24e6b641887b0cd9','Native identity')
 require(digest(dense)=='1ab0fd1fe7b727cc8841fcb32a2f20bec956d44b9b43b151c6a505da01721790','Dense identity')
 n,ns,nh=table(native);d,ds,dh=table(dense)
 require(len(n)==len(d)==392 and(ns,nh)==(74,254)and(ds,dh)==(0,196),'Census/start/halt')
 require(canonical(n,ns,nh)==canonical(d,ds,dh),'Dense renaming is not conjugate')
 old=from_rows(json.loads((ROOT/'data/source196.json').read_text()));rows=json.loads((ROOT/'data/variant196_source.json').read_text());new=from_rows(rows)
 require(statistics(new)==dict(internal_nodes=158,instructions=3812,maximum_depth=36,maximum_zero_run=7),'Source census')
 require(graph_by_intervals(new)==graph_by_bits(new)==graph_by_intervals(old)==graph_by_bits(old),'Source graph identity')
 require(rows[25][0]=='100000','Seed address')
 r,rs,rh=table(ROOT/'data/rejected195.native.tm')
 require(len(r)==390 and(rs,rh)==(74,254),'Rejected table census')
 changes={k:v for k,v in n.items()if r.get(k)!=v}
 require(changes=={(34,0):(0,'L',2000),(2000,0):(0,'L',75),(2000,1):(1,'L',2)},'Scanner repair delta')
 print(json.dumps(dict(status='VARIANT_FINITE_IDENTITIES_PASS',working_states=196,rows=392,source=statistics(new),source_cfg_rows=3812,dense_native_conjugate=True,scanner_repair_rows=len(changes),scope='Finite identity checks only; execute the separate symbolic runtime and blank-start checkers.'),indent=2))

if __name__=='__main__':main()
