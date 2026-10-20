#!/usr/bin/env python3
"""Selected Source145/146 leaf adapter; never calls delivered replay.main."""
import argparse,hashlib,importlib.util,json,sys
from pathlib import Path
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p,name):
    s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def dump(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
SPECS={
 'rho6_219':{'native':'031394d436b6b80708dcfb9e1b31938012c31aad94790bb3060ea63eae015f3b','source':'11f6694f72c65d7062998cc4419b8fd32452ceabe5637eee80e918cd2a2a72ec','leaves':4744,'depth':38,'cases':6167,'steps':1516088},
 'nop219':{'native':'90178e56e28c73fc3aec76751f94ef14cb567483d5536aaa127ce8c96d173db8','source':'4d09638d564a350bb7fe97a893bcd22dd6bc902d3f63ff674821aa1e87feb803','leaves':4750,'depth':37,'cases':6175,'steps':1508163}}
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--parent',type=Path,required=True);ap.add_argument('--runtime-inputs',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--variant',choices=SPECS,required=True);ap.add_argument('--mode',choices=['source','runtime'],required=True);a=ap.parse_args()
    assert __debug__ and not sys.flags.optimize
    supplied=load(a.packet/'verification/replay.py','submitted_replay_leaves')
    for n,h in supplied.DEPENDENCIES.items():assert sha(a.runtime_inputs/n)==h
    sys.path.insert(0,str(a.runtime_inputs/'portable'));import build221 as builder;import source_language as source
    sys.path.insert(0,str(a.runtime_inputs/'portable/runtime/vendor'));import symbolic_runtime as runtime
    spec=SPECS[a.variant];directory=a.packet/'machines'/a.variant
    assert sha(directory/'native.tm')==spec['native'] and sha(directory/'sites.json')==spec['source']
    table=builder.read_table((directory/'native.tm').read_bytes());rows=json.loads((directory/'sites.json').read_text());tree=source.tree(rows)
    states={q for q,b in table};assert len(states)==219 and len(table)==438 and set(table)=={(q,b) for q in states for b in (0,1)}
    assert 0 in states and 84 in states and 254 not in states and {z for w,d,z in table.values()}-states=={254}
    assert source.sites(tree)==rows and source.metrics(tree)=={'dag_nodes':206,'leaf_occurrences':spec['leaves'],'maximum_depth':spec['depth'],'maximum_zero_run':6}
    if a.mode=='source':
        a.output.mkdir(parents=True,exist_ok=False)
        oldraw=(a.parent/'machine/k219.native.tm').read_bytes();oldsitesraw=(a.parent/'machine/sites219.json').read_bytes()
        assert hashlib.sha256(oldraw).hexdigest()=='b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
        assert hashlib.sha256(oldsitesraw).hexdigest()=='0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
        old=builder.read_table(oldraw);oldsites=json.loads(oldsitesraw)
        assert set(old)==set(table)
        changes=[{'row':list(k),'old':list(old[k]),'new':list(table[k])} for k in sorted(old) if old[k]!=table[k]]
        if a.variant=='rho6_219':
            assert changes==[{'row':[199,1],'old':[1,1,166],'new':[1,1,12]},{'row':[206,0],'old':[0,1,186],'new':[0,1,76]}]
        else:assert len(changes)==38
        # This is exact decoder binding, not a state-count-only acceptance gate.
        binding=builder.decoder_map(table,tree)
        sm={int(q):int(z) for q,z in json.loads((directory/'state_map.json').read_text()).items()}
        assert set(sm)==states|{254} and set(sm.values())==set(range(220)) and (sm[0],sm[84],sm[254])==(0,23,219)
        canonical={(sm[q],b):(w,d,sm[z]) for(q,b),(w,d,z) in table.items()}
        assert builder.table_bytes(canonical)==(directory/'canonical.tm').read_bytes()
        sr=supplied.source_rho6(source,oldsites,rows) if a.variant=='rho6_219' else supplied.source_nop(source,oldsites,rows,a.output)
        boot=supplied.boot(table)
        dump(a.output/'source.json',sr);dump(a.output/'startup.json',boot)
        dump(a.output/'binding.json',{'status':'EXACT_DECODER_AND_CANONICAL_BINDING_PASS','table_sha256':spec['native'],'source_sha256':spec['source'],'canonical_sha256':sha(directory/'canonical.tm'),'source_metrics':source.metrics(tree),'states':219,'rows':438,'changed_rows':changes})
        print(a.variant,sr['status'],boot['status'],flush=True)
    else:
        assert (a.output/'binding.json').is_file()
        rec=supplied.runtime_check(table,rows,a.runtime_inputs,a.output,runtime)
        assert (rec['cases'],rec['symbolic_steps'])==(spec['cases'],spec['steps']) and rec['minimum_duration_constant']>0
        cases=json.loads((a.output/'runtime_cases.json').read_text());expected=[(i,p) for i,(_,op,arg) in enumerate(rows) for p in ((False,True) if op=='CD' else (False,))]
        assert [(x['index'],x['positive']) for x in cases]==expected
        assert all(len(x['duration'])==13 and all(type(y)is int and y>=0 for y in x['duration']) and x['duration'][0]>0 for x in cases)
        delivered=a.packet/'verification/recorded'/a.variant/'runtime_cases.json'
        assert (a.output/'runtime_cases.json').read_bytes()==delivered.read_bytes()
        dump(a.output/'runtime.json',rec)
        dump(a.output/'runtime-comparison.json',{'status':'FRESH_EXACT_ORDERED_CASE_REPLAY_PASS','cases':len(cases),'case_sha256':sha(a.output/'runtime_cases.json'),'exact_delivered_case_bytes':True,'positive_affine_durations':True,'no_claim':'This driver does not report all-row coverage; no all438-row claim is inferred.'})
        print(a.variant,rec['status'],rec['cases'],rec['symbolic_steps'],flush=True)
if __name__=='__main__':main()
