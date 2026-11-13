#!/usr/bin/env python3
"""Read-only focused endpoint and stage-079 artifact audit; no Lean replay."""
import hashlib
import json
import os
from pathlib import Path
import re
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('run with python3 -I -S -B')
ROOT=Path(__file__).resolve().parents[2]
PK=ROOT/'research/normalized106-historical-endpoint-client'
OBS=PK/'observations/attempt01'
CHAIN=ROOT/'reviews/nine-variable-ipra-equal-length-stages-77-81-overlap/observations/stages-077-081'
BIND=ROOT/'research/normalized106-graph-syntax-binding'
OUT=Path('/tmp/normalized106-historical-endpoint-priority-check01')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(ok,msg):
    if not ok:raise RuntimeError(msg)
pins={
 PK/'Normalized106EndpointCheck.lean':'f2d1d17416a159be82405a96b0abefb17e2a02a57608fa86f2a2b0f02009a5a6',
 PK/'check01.py':'3e20b2e3c13a7bf49840639dd767baaa6ad7f7856f0349b33fc9c18a8392db03',
 OBS/'compile.log':'029eeebcb3b2eff02816593067fb1ee4c5db3d0a98c6c1e63c468d66852a28d3',
 OBS/'result.json':'0f7db0f46fc34fd52ebdac20253f9f22761c0c38ff04fce2241e3d59aa537112',
 OBS/'outer-terminal.json':'3905c27ef88a36e011c1cc402b0420e4c5c7b0e74ad29f347478b49f1b3fe725',
 CHAIN/'author/079/receipt.json':'33f040272cf2bc0203e21521ba20d5499bb6c39adc8de02e817a2e41b334318d',
 CHAIN/'verify/079/receipt.json':'cca6416a35445492c917132c250eed00ffc099a97f2bc9daed34908f193d678e',
 CHAIN/'terminal.json':'6caef4771720124c2fd6612df8f76758ae68eef97211c129fde431f53ace84d8',
 CHAIN/'audit.json':'273dabc30b4e5a83c9875788245f378dbf6b6505b8dd008274a2728bc117964a',
 CHAIN/'author/078/receipt.json':'00300fc41cf787db439a99d4afe49e0d14cffd1aa4fad505a3ad18aac750e420',
 CHAIN/'author/078/ModelCarrierSyntax.lean':'8d40486fd9adf151e905977c01cbc1a2aa7142fbd02c5e4293906c6865e5a43a',
 BIND/'check.py':'3d36c67101606c5d0d8b1e47c0c00fa06e5eceb0370a1baa4b086b5017128c65',
 BIND/'result.json':'2ea08d98108465c1d1e48e1296e32a2f15aceebadae682231c00b87e8c00d552',
 BIND/'outer-terminal.json':'ede299f578e43719e4e673307fd95b7626a05298b8e96e717f25746ec03234f3',
 ROOT/'research/fourteen-normalized-product106/polynomial.json':'0485cd1e884b918d766261b1780be117238f0813a965c6d8ae4d805176a5f6e1',
}
for path,h in pins.items():require(path.is_file() and sha(path)==h,'pin mismatch '+str(path))
result=json.loads((OBS/'result.json').read_text());outer=json.loads((OBS/'outer-terminal.json').read_text())
require((OUT/'result.json').read_bytes()==(OBS/'result.json').read_bytes(),'terminal result mismatch')
require((OUT/'compile.log').read_bytes()==(OBS/'compile.log').read_bytes(),'terminal log mismatch')
require(result['status']=='PASS' and result['exit']==0 and result['stop_reason'] is None and
        result['guards_stable'] and result['guards_before']==result['guards_after'],'failed receipt')
require(outer['terminal_exit_code']==0 and outer['session_id']==4715 and
        outer['returned_session_id'] is None,'outer completion not observed')
require(result['group_rss_samples']>0 and result['minimum_memavailable_bytes']>=10*1024**3 and
        result['sampled_peak_group_rss_bytes']<7*1024**3//2,'resource condition failed')
obj=OUT/'Normalized106EndpointCheck.olean'
require(obj.is_file() and not obj.is_symlink() and sha(obj)==result['object_sha256']==
        '0b0ebabc40c3b716b31656b1c7e4a22928e5017f58296db5e7dcad59f22d93c8','output mismatch')

producer=json.loads((CHAIN/'author/079/receipt.json').read_text())
peer=json.loads((CHAIN/'verify/079/receipt.json').read_text())
audit=json.loads((CHAIN/'audit.json').read_text());terminal=json.loads((CHAIN/'terminal.json').read_text())
require(producer['status']==peer['status']=='PASS' and terminal['exit_code']==0 and
        audit['status']=='EQUAL_LENGTH_PREFIX_SCOPED_COMPARISON_PASS','producer/replay failed')
expected_source='f0a4898f545a932b135783799ae0d44179fbcbcb08e5d97eaced4515740e990f'
expected_object='79bf09c3051ad06f55abdd511c7310ccd795856f1275b6b23836f8b535e74122'
for item in (producer,peer):
    require(item['module']=='DiophantineConsistency.ModelCarrierCurrent' and
            item['source_sha256']==expected_source and item['output']['sha256']==expected_object,
            'stage-079 source or object mismatch')
for p in [ROOT/'Lean/DiophantineConsistency/ModelCarrierCurrent.lean',
          CHAIN/'author/079/ModelCarrierCurrent.lean',CHAIN/'verify/079/ModelCarrierCurrent.lean']:
    require(sha(p)==expected_source,'stage source differs '+str(p))
stage=next(s for s in audit['stages'] if s['module']=='DiophantineConsistency.ModelCarrierCurrent')
require(stage['stage']==79 and stage['comparison']=='byte-identical' and
        stage['direct_guard_count']==360 and stage['source_sha256']==expected_source and
        stage['author_object_sha256']==stage['verify_object_sha256']==expected_object,'stage comparison mismatch')
diff=stage['direct_input_differences']
require(len(diff)==1 and diff[0]['module']=='DiophantineConsistency.ModelCarrierScaled' and
        diff[0]['author_sha256']!=diff[0]['verify_sha256'],'lost direct provider qualification')
require(len(producer['direct_guards'])==360,'producer guard count')
syntax=json.loads((CHAIN/'author/078/receipt.json').read_text())
binding=json.loads((BIND/'result.json').read_text())
require(syntax['status']=='PASS' and syntax['module']=='DiophantineConsistency.ModelCarrierSyntax' and
        syntax['source_sha256']==binding['lean_source_sha256'] and
        syntax['output']['sha256']==producer['direct']['DiophantineConsistency.ModelCarrierSyntax']['record']['sha256'] and
        binding['status']=='PASS' and binding['output_equal_mod_ac'] and binding['live_rows']==67 and
        binding['graph_sha256']==pins[ROOT/'research/fourteen-normalized-product106/polynomial.json'] and
        json.loads((BIND/'outer-terminal.json').read_text())['terminal_exit_code']==0,
        'external graph binding/source chain mismatch')

# Recheck all captured slots. 360 originate in the stage-079 receipt; the
# remainder guard the focused source, producer evidence, binary and providers.
guards=result['guards_before'];guard_count=0
for key,record in guards.items():
    path=Path(key.removeprefix('producer:'))
    if record is None:
        require(not os.path.lexists(path),'absent slot appeared '+str(path))
    else:
        require(path.is_file() and sha(path)==record['sha256'],'guard bytes differ '+str(path))
        resolved=record.get('resolved',record.get('realpath'))
        require(str(path.resolve())==resolved,'guard resolution differs '+str(path))
        if 'link' in record:require((os.readlink(path) if path.is_symlink() else None)==record['link'],
                                    'guard link differs '+str(path))
    guard_count+=1
for name,record in producer['direct_guards'].items():
    require(guards['producer:'+name]==record,'focused guard does not match producer slot')
require(len(guards)==378 and guard_count==378,'unexpected focused guard count')

log=(OBS/'compile.log').read_text()
names=['DiophantineConsistency.ModelCarrierCurrent.'+n for n in
       ('sameZero106','bridge106','standard_equivalence106')]
reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
require(len(reports)==3 and [n for n,_ in reports]==names,'axiom report declarations')
for name,axioms in reports:
    require([a.strip() for a in axioms.split(',')]==['propext','Classical.choice','Quot.sound'],
            'unexpected axiom set '+name)
require(not any(x in log for x in ('sorryAx','warning:','error:')),'compiler diagnostic')
prefix=log.split("'"+names[0]+"' depends on axioms:")[0]
for n in names:require(prefix.count(n)==1,'missing or duplicated #check '+n)
for fragment in ('[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(v : Fin 14 → V)',
                 'ObjectCurrentEquation2011.naturalExpression v',
                 'HAExpressionAssembly.PolynomialBridge',
                 'IPRAStandardTheory.standardTheory ⊢',
                 'IPRAExpressionNative.nativeNoZero',
                 'IPRAFoundationZFCMappedNegation.mappedNativeRefutation'):
    require(fragment in prefix,'missing theorem type fragment '+fragment)
require(prefix.count('ModelCarrierCurrent.expressionAt106')==3 and
        prefix.count('CurrentWindowCarry2011.ports')==3,'wrong expression or tuple')
print(json.dumps({'status':'PASS_DIRECT_ARTIFACT_AND_TYPE_AUDIT','focused_guards_checked':guard_count,
 'producer_slots_checked':len(producer['direct_guards']),'axiom_reports_checked':len(reports),
 'stage79_modelcarrierscaled_direct_provider_differs':True,'lean_replayed':False,
 'scope':'Historical stage-079 direct provider, three printed theorem types and axiom reports; '
         'transitive/package/dynamic ancestry and JSON/PDF bindings remain separate.'},sort_keys=True))
