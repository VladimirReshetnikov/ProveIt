from pathlib import Path
import gzip,hashlib,json,subprocess,sys
D=Path(__file__).resolve().parents[2];h=D/'research/trace74-fixed-bfs-nocarry-obstruction';scalar=D/'research/trace74-fixed-bfs-scalar-boundary';coef=D/'candidates/ten-positive-qcube-product-square/coefficients'
def sha(b):return hashlib.sha256(b).hexdigest()
assert sha((h/'check.py').read_bytes())=='60aa48d0493825856a00d34053730e0208c4aff19e74c6e4febd30d1fc0802f8' and sha((h/'observation.json').read_bytes())=='502788636f540fcaadbd8a4ca080afc198724eea044deb228ff1cf7334d69087';assert sha((scalar/'observation.json').read_bytes())=='2bc1bc720ff7efc6ecb29ddaf823705fcae730415eeceaaedb0cbcff2e0e843b';a=json.loads((scalar/'observation.json').read_text());assert (a['J'],a['F'],a['C'],a['guard'])==(1,3,'q-3','F+C=q')
z=subprocess.run([sys.executable,'-I','-S','-B',str(h/'check.py')],capture_output=True,text=True);assert z.returncode==0 and not z.stderr and json.loads(z.stdout)==json.loads((h/'observation.json').read_text())
vals={}
for n,gzsha,rawsha in [('beta','07d42a69e7593ac08bcb2957c965c02f179588b0c3b232c3c640258d0aaeab04','0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d'),('MC','71ecc4fe568471f83978d00ee7a4e03614203d6af36611c0660dbd4fd3eb2276','6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4')]:
 blob=(coef/(n+'.bin.gz')).read_bytes();assert sha(blob)==gzsha;raw=gzip.decompress(blob);assert sha(raw)==rawsha;vals[n]=int.from_bytes(raw,'little')
q=vals['beta']+1;mc=vals['MC'];assert q==2**590069 and mc%2**67==2**67-2;C=q-3;assert 3+C==q and (C-1)%8==4 and (mc+1)%8==7;assert ((C-1)//4)%2==((mc+1)//4)%2==1 and 2<(C-1)+(mc+1)+1
print('PASS pinned beta/MC payloads; (C-1) mod8=4, (MC+1) mod8=7, shared bit2 obstructs NoCarry for scalar assignment only')
