import importlib.util,sys,json,hashlib,argparse
from pathlib import Path
ap=argparse.ArgumentParser(description='Replay the exact small primitive-certificate CA orbit')
ap.add_argument('--source',required=True);ap.add_argument('--compiler',required=True);ap.add_argument('--output',required=True)
args=ap.parse_args();p=Path(args.compiler)
if hashlib.sha256(p.read_bytes()).hexdigest()!='f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f':raise RuntimeError('Compiler pin mismatch')
spec=importlib.util.spec_from_file_location('root_ca',p);mod=importlib.util.module_from_spec(spec);sys.modules[spec.name]=mod;spec.loader.exec_module(mod)
src=Path(args.source).read_bytes()
if hashlib.sha256(src).hexdigest()!='96321c1051285d90f2bec9a8915976b370400ae0826aed886c34e04ada4c468d':raise RuntimeError('Example source pin mismatch')
c=mod.compile_source(json.loads(src));x0=c.encode(c.start,0,0);x=x0
want={0,c.S,c.S+c.gap[(('H',c.halt),'+')]};hits=[];returns=[];frames=[]
for t in range(6232):
 if len(x)!=5: raise RuntimeError('mass')
 if {a for a in x if 0<=a<=c.S+c.D}==want: hits.append(t)
 if t and x==x0: returns.append(t)
 frames.append(sorted(x));x=c.step(x)
if x!=x0 or returns or hits!=[3115]:raise RuntimeError((x,returns,hits))
if frames[3115]!=sorted(c.encode(c.halt,0,0)):raise RuntimeError('target')
out=Path(args.output);out.mkdir(parents=True,exist_ok=True)
(out/'primitive-example-orbit.json').write_text(json.dumps({'source_sha256':hashlib.sha256(src).hexdigest(),'input_counters':[0,0],'frames':frames,'next_frame':sorted(x)},separators=(',',':'))+'\n')
r={'status':'passed','source_sha256':hashlib.sha256(src).hexdigest(),'compiler_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'ca_steps_executed':6232,'first_halt':3115,'least_return':6232,'mass':5,'ledger':c.ledger()}
(out/'primitive-example-ca-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
