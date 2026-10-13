#!/usr/bin/env python3
"""Replay frozen delivered certificates without replacing them."""
import sys,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from pivotwidth.transfer_verify import verify_power
from pivotwidth.verify import replay,transport

if __name__=='__main__':
    huge=json.loads((ROOT/'results'/'huge_power_certificate.json').read_text())
    checked=verify_power(huge)
    assert huge['exponent']==1<<1024
    assert checked['deferred_weight']==3*(1<<1024)
    packet=json.loads((ROOT/'examples'/'small_plan.json').read_text())
    replay(packet['matrix'],packet['weights'],packet['certificate'])
    packet=json.loads((ROOT/'examples'/'minimum_fill_counterexample.json').read_text())
    result=replay(packet['matrix'],packet['weights'],packet['optimal_certificate'])
    assert result['retained_weight']==3
    assert all(sum(row[j] for row in packet['matrix'])==3 for j in range(4))
    assert transport(packet['matrix'],result['schedule'])==packet['exact_passive_transport']
    print(json.dumps({'status':'PASS','frozen_power_nodes':checked['proof_nodes'],
                      'exponent':'2^1024','small_plan':'PASS','minimum_fill_counterexample':'PASS'},indent=2))
