#!/usr/bin/env python3
"""Independent finite AQ22 endpoint/graph and saved-port review."""
import gzip
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
if not __debug__: raise RuntimeError('optimized Python is unsupported')
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REV=ROOT/'reviews'
ORIG=REV/'aq22-pdf-historical-lean-binding'
AUTH=REV/'ipra-aq22-guarded-author'
GRAPH=ROOT/'research/adaptive-square-sums22-degree10/candidate.json'
SNAP=Path('/tmp/ipra-aq29-fresh-source-closure-v2/src/DiophantineConsistency')
PARENT=Path('/tmp/ipra-aq29-fresh-project-pair/author/state.json')
PORT=REV/'equation14-historical-literal-binding'
PORT_REVIEW=REV/'equation14-historical-literal-binding-independent'
CARRIER=ROOT/'candidates/one-page-padding-staircase-carrier65-2011'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
J=lambda p:json.loads(Path(p).read_text())
original=J(ORIG/'receipt.json'); state=J(AUTH/'state.json'); parent=J(PARENT); c=J(GRAPH)
literal=AUTH/'src/DiophantineConsistency/AdaptiveAQ22Literal.lean'
endpoint=AUTH/'src/DiophantineConsistency/IPRAStandardAQ22.lean'
inputs=[Path(__file__),ORIG/'audit.py',ORIG/'receipt.json',ORIG/'terminal-observation.json',literal,endpoint,GRAPH,
        AUTH/'state.json',AUTH/'terminal-exit.json',PARENT,SNAP/'CurrentKernelData2011.lean',
        SNAP/'AdaptiveEquationSyntax2011.lean',SNAP/'IPRAExpressionNative.lean',
        PORT/'ports-receipt.json',PORT/'printed-constants-repeat.json',PORT_REVIEW/'receipt.json',
        PORT_REVIEW/'terminal-observation.json',CARRIER/'polynomial.json']
carrier=J(CARRIER/'polynomial.json')
for i,name in enumerate(c['fixed_numerals']):
    inputs.extend((PORT/'port-outputs'/f'port{i}.txt.gz',CARRIER/'coefficients'/carrier['coefficient_binding']['ports'][name]['file']))
before={str(p.resolve()):H(p) for p in inputs}
assert H(ORIG/'audit.py') == original['inputs_sha256'][str((ORIG/'audit.py').resolve())]
assert J(ORIG/'terminal-observation.json')['ordinary_python_exit_code']==0
assert state['parent_state_sha256']==H(PARENT)==original['historical_author_parent_sha256']
assert state['status']=='AUTHOR_ONLY_PASS' and parent['status']=='PASS'
assert J(AUTH/'terminal-exit.json')['returncode']==0
# Independently parse the complete literal into a graph, not line generation.
s=literal.read_text(); marker='def literal (p : Fin 4 → ℤ) : Expr (Fin 22) :='
assert s.count(marker)==1
body=s.split(marker,1)[1].split('\nend DiophantineConsistency.AdaptiveAQ22Literal',1)[0].strip().splitlines()
variables=[];ports=[];ops=[];ret=None
for line in body:
    line=line.strip()
    m=re.fullmatch(r'let (\w+) : Expr \(Fin 22\) := \.var (\d+)',line)
    if m: variables.append((m[1],int(m[2])));continue
    m=re.fullmatch(r'let (\w+) : Expr \(Fin 22\) := \.constant \(p (\d+)\)',line)
    if m: ports.append((m[1],int(m[2])));continue
    m=re.fullmatch(r'let (\w+) := (\w+) ([+*\-]) (\w+)',line)
    if m: ops.append([m[1],m[3],int(m[2]) if m[2].isdigit() else m[2],int(m[4]) if m[4].isdigit() else m[4]]);continue
    assert ret is None and re.fullmatch(r'\w+',line);ret=line
assert variables==list(zip(c['witnesses'],range(22))) and len(set(c['witnesses']))==22
assert ports==list(zip(c['fixed_numerals'],range(4)))
assert ops==c['source'] and len(ops)==114 and ret==c['output']
e=endpoint.read_text(); theorem=re.search(r'theorem literal_iff_translated_consistency\s*:\s*(.*?)\s*:=',e,re.S)
assert theorem and re.sub(r'\s+',' ',theorem[1]).strip() == ('standardTheory ⊢ IPRAExpressionNative.nativeNoZero '
 '(positiveShift (AdaptiveAQ22Literal.literal CurrentWindowCarry2011.ports)) 🡘 '
 '(Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ')
assert 'e.subst (fun i => Expr.var i + Expr.constant 1)' in (SNAP/'AdaptiveEquationSyntax2011.lean').read_text()
assert 'def ports : Fin 4 → ℤ := CurrentMasks2011.ports (K : ℤ)' in (SNAP/'CurrentKernelData2011.lean').read_text()
# Independently check each edge of the recorded paths, including source/object
# rows, while retaining the distinction between recorded guards and load trace.
rows={r['module']:r for r in parent['records']};rows.update({r['module']:r for r in state['rows']})
for file,name in ((literal,'AdaptiveAQ22Literal'),(endpoint,'IPRAStandardAQ22'),
                  (SNAP/'CurrentKernelData2011.lean','CurrentKernelData2011')):
    assert rows['DiophantineConsistency.'+name]['source_sha256']==H(file)
for pathkey,end in [('literal_recorded_import_path','AdaptiveAQ22Literal'),('port_recorded_import_path','CurrentKernelData2011')]:
    path=original[pathkey];assert path[0]=='DiophantineConsistency.IPRAStandardAQ22' and path[-1]=='DiophantineConsistency.'+end
    for a,b in zip(path,path[1:]):
        row=rows[a]; edge=row.get('imports',row.get('direct_inputs',{}))[b]
        assert edge['sha256']==rows[b]['object_sha256'] and row['exit']==0
kernel=rows['DiophantineConsistency.CurrentKernelData2011']['object_sha256']
guards=[v['sha256'] for k,v in state['overlay_guards'].items() if k.endswith('/CurrentKernelData2011.olean')]
assert guards==[kernel]
prior=J(PORT_REVIEW/'receipt.json');probe=J(PORT/'ports-receipt.json');printed=J(PORT/'printed-constants-repeat.json')
assert prior['status']=='PASS_INDEPENDENT_FINITE_BINDING_REVIEW'
assert J(PORT_REVIEW/'terminal-observation.json')['observed_exit_code']==0
assert prior['fresh_probe_exit']==prior['fresh_probe_deps_exit']==prior['recipe_rerun_exit']==0
assert probe['parent_state_sha256']==H(PARENT) and probe['kernel_data_object_sha256']==kernel
assert printed['result']=='PASS' and printed['tile_rows']==942 and printed['rank_comparisons']==885481
port_records=[]
for i,name in enumerate(c['fixed_numerals']):
    meta=carrier['coefficient_binding']['ports'][name];binary=gzip.decompress((CARRIER/'coefficients'/meta['file']).read_bytes())
    decimal=gzip.decompress((PORT/'port-outputs'/f'port{i}.txt.gz').read_bytes())
    value=int(decimal); assert value==int.from_bytes(binary,'big') and str(value).encode()==decimal
    digest=hashlib.sha256(binary).hexdigest(); assert digest==meta['raw_sha256']==prior['ports'][i]['integer_sha256']==probe['ports'][i]['integer_sha256']
    assert hashlib.sha256(decimal).hexdigest()==probe['ports'][i]['decimal_sha256']==prior['ports'][i]['decimal_sha256']
    port_records.append({'name':name,'digits':len(decimal),'integer_sha256':digest})
# Execute the exact original audit from a temporary sibling directory, so its
# root and paths resolve as designed without modifying its saved packet.
with tempfile.TemporaryDirectory(prefix='aq22-binding-independent-repeat-',dir=REV) as td:
    temp=Path(td);shutil.copy2(ORIG/'audit.py',temp/'audit.py')
    assert H(temp/'audit.py')==H(ORIG/'audit.py')
    normal=subprocess.run([sys.executable,str(temp/'audit.py')],capture_output=True,text=True,timeout=180)
    assert normal.returncode==0,(normal.stdout,normal.stderr)
    replay=J(temp/'receipt.json');assert replay['status']==original['status']
    for key in ('variables','fixed_ports','gates','literal_mutations_rejected','port_decimal_mutations_rejected',
                'literal_recorded_import_path','port_recorded_import_path','historical_author_parent_sha256','pdf_sha256'):
        assert replay[key]==original[key],key
    optimized=[]
    for flag in ('-O','-OO'):
        q=subprocess.run([sys.executable,flag,str(temp/'audit.py')],capture_output=True,text=True,timeout=30)
        assert q.returncode!=0 and 'optimized Python is unsupported' in q.stderr
        optimized.append({'flag':flag,'returncode':q.returncode,'stderr':q.stderr})
    original_rerun={'returncode':normal.returncode,'stdout':normal.stdout,'stderr':normal.stderr,
                    'receipt_sha256':H(temp/'receipt.json'),'optimized':optimized}
assert {str(p.resolve()):H(p) for p in inputs}==before
result={'status':'PASS_INDEPENDENT_AQ22_FINITE_BINDING_REVIEW','inputs_sha256':before,
        'variables':len(variables),'ports':port_records,'operations':len(ops),'replayed_original':original_rerun,
        'scope':'Historical author endpoint, recorded direct imports and finite graph/print/port evidence. No new Lean endpoint or port computation; no internal TeX semantics. Decoder/table/rank/port recipe remains manually transcribed. No paired replay or current-source claim.'}
out=HERE/'receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(result['status'],H(out))
