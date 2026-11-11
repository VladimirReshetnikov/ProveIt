from pathlib import Path
import hashlib,subprocess,sys,json
root=Path(__file__).resolve().parents[2];a=root/'research/current14-k215-wf-chunk-probe-draft/KSource215WfChunk00.lean';b=root/'research/current14-k215-wf-last-chunk-draft/KSource215WfChunk15.lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(a)=='095986b8cbfdad47f8740983db20e59ecb366098f343f35efeee64c6891b170e'
assert sha(b)=='ff050e5fb63fef00566dba6e73093ddcdee7f081f3115172bc88f86653838ec0'
x=a.read_text();y=b.read_text();x=x.replace('First 32 actual DAG-node checks; the other 455 nodes and assembly are separate.','Last seven actual DAG-node checks; other nodes and assembly remain separate.').replace('wfChunk00','wfChunk15').replace("List.range' 0 32","List.range' 480 7");assert x==y
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-k215-wf-chunk-probe-terminal-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_SOURCE_ONLY','checked_indices':'480..486','lean_run':False,'scope':'first and last chunks only; intermediate nodes, root facts and assembly open'},indent=2))
