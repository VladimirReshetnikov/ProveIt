#!/usr/bin/env python3
"""Run the exact fake wrapper's success case with added receipt assertions."""
import hashlib,pathlib,re,subprocess,sys,tempfile
p=pathlib.Path('Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-wang-table-chunk-explore').resolve();f=p/'full-fake-controls.py';src=f.read_text();assert hashlib.sha256(f.read_bytes()).hexdigest()=='dfeee65490eb8fbb4acc578f6d11333d0a2050bcfd4edc5bfbb1d07e4d0dca31'
src=src.replace('ROOT=Path(__file__).resolve().parent',f'ROOT=Path({str(p)!r})',1);src,n=re.subn(r'^modes=\[.*\]$',"modes=['success']",src,count=1,flags=re.M);assert n==1
anchor="   guard=data['final_direct_and_output_slots'];need(guard[str(output/'lib/Init.olean')] is None and guard[str(output/'lib/Init.olean.private')] is None and guard[str(pkg/'Init.olean')] is not None,'missing candidate-root guard')"
extra="""   manifest=json.loads((ROOT/'source-manifest.json').read_text())['sources']
   need([x['module'] for x in data['steps']]==[x['module'] for x in manifest],'order mismatch')
   for step,row in zip(data['steps'],manifest):
    name=row['module']; source=(output/'frozen'/Path(*name.split('.'))).with_suffix('.lean'); obj=(output/'lib'/Path(*name.split('.'))).with_suffix('.olean')
    command=[str(lean),'-M3000','-j1','-DElab.async=false','--root='+str(output/'frozen'),str(source),'-o',str(obj)]
    need(step['compiler_command']==command and step['deps_command']==[str(lean),'--deps',str(source)],('exact command',name))
    need(len(step['output_slots'])==10 and step['output_slots'][str(obj)] is not None and all(value is None for path,value in step['output_slots'].items() if path!=str(obj)),('exact output slots',name))
    need(H(obj)==step['output_slots'][str(obj)]['sha256'] and H(Path(step['log']))==step['log_sha256'],('output/log bytes',name))
    names=__import__('re').findall(r'^#print\\s+axioms\\s+([\\w.]+)\\s*$',source.read_text(),__import__('re').M)
    need(set(names)==set(step['axiom_reports']),('report names',name))
"""
assert anchor in src;src=src.replace(anchor,anchor+'\n'+extra.rstrip(),1)
with tempfile.TemporaryDirectory(prefix='wang-independent-control-') as t:
 script=pathlib.Path(t)/'extended.py';script.write_text(src);r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],capture_output=True,text=True,timeout=180)
 assert r.returncode==0,(r.returncode,r.stdout,r.stderr)
 print('PASS_INDEPENDENT_EXACT_96_COMMANDS_OUTPUTS_AND_FAKE_REPORT_NAMES; no Lean')
