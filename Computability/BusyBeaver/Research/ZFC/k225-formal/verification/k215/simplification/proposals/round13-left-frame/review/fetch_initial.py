import pathlib,json,urllib.request,concurrent.futures
D=pathlib.Path('research215_round13_review'); pin=json.loads((D/'PINS.json').read_text())['pin']; pre='Computability/BusyBeaver/Research/ZFC/k225-formal/'; tree=json.loads((D/'VERIFICATION_TREE.json').read_text())['tree']; paths=[pre+'verification/'+x['path'] for x in tree if x['type']=='blob' and any(y in x['path'] for y in ['/phase13/','/phase14/','/enum-contracts/','/ax-word/']) and x['path'].endswith(('README.md','result.json','current-review.json','index.json','execution.tar.gz'))]; paths += [pre+'verification/k215/simplification/README.md',pre+'verification/k215/simplification/proposals/README.md',pre+'README.md',pre+'Source215.v',pre+'EnumPerm.v',pre+'DomRho8.v']; paths += ['Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'+n+'.lean' for n in ['DominatedImplication','Lukasiewicz','EnumDom','SeedDom','KThmK','KDenseBridge','KSim','KRuntimeCore','KDecoderPrefix215','KSeed222','KSeedModel222','L2AxiomsDom','L2RootDom','ZFModels','QHyp','PowerSets']]
def f(p):
 try:
  b=urllib.request.urlopen('https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/'+pin+'/'+p).read();q=D/'current'/p;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b);return p
 except Exception as e:return 'ERROR '+p+': '+str(e)
with concurrent.futures.ThreadPoolExecutor(max_workers=12) as e:
 for p in e.map(f,paths):print(p,flush=True)
