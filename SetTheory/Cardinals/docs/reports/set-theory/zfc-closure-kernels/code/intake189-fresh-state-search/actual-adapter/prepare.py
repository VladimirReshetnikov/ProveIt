#!/usr/bin/env python3
import hashlib,json,shutil,sys
from pathlib import Path
B=Path('/tmp/zfc-intake189-opening');E=B/'execution'
P=Path('/tmp/zfc-intake188/drop-review/ZFC_218_State_Search_2026-10-20/ZFC_218_State_Search_2026-10-20')
def desc(p):return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def main():
    assert not E.exists();E.mkdir();packet=E/'packet';shutil.copytree(P,packet)
    prior=Path('/tmp/zfc-intake188-opening/execution');parent=E/'parent219';runtime=E/'runtime-inputs';out=E/'output';out.mkdir()
    # Reuse only exact already recovered data/engines, not any ancestor execution.
    shutil.copytree(prior/'baseline/K219_Construction_2026-10-20/machine',parent/'machine')
    shutil.copytree(prior/'runtime-inputs/K221_Construction_2026-10-20',runtime)
    py=sys.executable;direct=B/'review/direct.py'
    jobs=[{'name':'01_closed_rho6_subtrees','argv':[py,'-B',str(packet/'verification/check_source_closure.py'),'--output',str(out/'rho6-closure.json')],'timeout_seconds':60}]
    for index,(variant,mode) in enumerate([('rho6_219','source'),('nop219','source'),('rho6_219','runtime'),('nop219','runtime')],2):
        argv=[py,'-B',str(direct),'--packet',str(packet),'--parent',str(parent),'--runtime-inputs',str(runtime),'--output',str(out/variant),'--variant',variant,'--mode',mode]
        jobs.append({'name':f'{index:02}_{variant}_{mode}','argv':argv,'timeout_seconds':240 if mode=='runtime' else 60})
    inputs=[direct,packet/'verification/replay.py',packet/'verification/check_source_closure.py',packet/'vendor/K219_Construction_2026-10-20.zip']
    inputs += [p for p in sorted(runtime.rglob('*')) if p.is_file()]
    inputs += [parent/'machine/k219.native.tm',parent/'machine/sites219.json']
    inputs += [packet/'machines'/v/n for v in ('rho6_219','nop219') for n in ('native.tm','canonical.tm','sites.json','state_map.json')]
    plan={'status':'REVIEWED_SELECTED_LEAVES_READY','jobs':jobs,'cwd':str(packet),'inputs':[desc(p) for p in inputs],'scope':'Two distinct219state variants: exact source/decoder/canonical binding, dual blank startup, full arbitrary-value symbolic runtime and ordered case comparison; source-only relative calibration separately reviewed.','exclusions':['No delivered replay.main or wrapper invocation','No manifest or checksum-suite invocation','No ancestor-suite replay','No Rocq/Coq/Lean or broad search execution']}
    (E/'plan.json').write_text(json.dumps(plan,indent=2)+'\n');print(E/'plan.json')
if __name__=='__main__':main()
