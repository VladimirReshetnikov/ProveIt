import match_macros2 as m
b=m.b
wanted=['a','b','c','all','mem','ex','and','neg','im','1','push','read_b','read_s1','s1_top','ac_s1s2','ifeq_clrtop','s2_s1','a_b','top_clear']
# Add exactly rewritten eq test by replacing transfer+1.
old=((('CD',6),(('CI',5),('CC',2))),('CI',5))
new=(('CI',5),(('CD',6),('CC',2)))
def rewrite(n):
 if n==old:return new
 return n if b.is_leaf(n) else tuple(map(rewrite,n))
macros={}
for i,name in m.e.names.items():
 if name not in wanted:continue
 n=m.e.expand(('N',i));f=m.fingerprint(rewrite(n))
 for nn in m.byfinger.get(f,[]):macros[nn]=name
rows=[]
def walk(n,p=''):
 if n in macros:rows.append((p,macros[n],n));return
 if b.is_leaf(n):rows.append((p,n,n));return
 walk(n[0],p+'0');walk(n[1],p+'1')
walk(m.root)
if __name__=='__main__':
 for i,(p,name,n) in enumerate(rows): print(i,p,name)
