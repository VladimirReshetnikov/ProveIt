from pathlib import Path
import search_generic as G
import search_future as F
S=G.S;m=S.load_machine()
ctx={q:set()for q,b in m}
for q,prev in[(0,0),(75,1)]:ctx[q]={t for t in range(512)if(t>>3)&1==prev}
for module in[G,F]:
 src=Path(module.__file__).read_text().split("if __name__=='__main__':")[0]
 src=src.replace('can=[q for q in qs if q not in protected]','can=[0,75]')
 ns={'__file__':module.__file__};exec(src,ns)
 print(module.__name__,ns['candidates'](m,ctx),flush=True)
