from pathlib import Path
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
# ed. (2026-09-29): embed TrueType (Type 42) fonts instead of Type 3 in the PDF figure.
matplotlib.rcParams['pdf.fonttype']=42
matplotlib.rcParams['ps.fonttype']=42
import matplotlib.pyplot as plt
from verify import coeffs_c,mpr
mp.mp.dps=100
X=mp.mpf(10); a=X-1/(12*X)
c=[mpr(x) for x in coeffs_c(61)]
w=mp.findroot(lambda z:mp.digamma(z+mp.mpf('.5'))-mp.log(X),(a,X))
orders=list(range(1,61)); errors=[]; bounds=[]
for M in orders:
    u=mp.findroot(lambda z:mp.log(z/X)+mp.fsum(c[j]*z**(-2*j) for j in range(1,M+1)),(a,X))
    errors.append(float(abs(u-w)))
    bounds.append(float((X+mp.mpf('.5'))*abs(c[M+1])/a**(2*M+2)))
fig,ax=plt.subplots(figsize=(7.2,4.1))
ax.semilogy(orders,errors,label='Actual implicit-inverse error',linewidth=1.8)
ax.semilogy(orders,bounds,'--',label='Analytic certificate bound',linewidth=1.5)
ax.axvline(float(mp.pi*X),linestyle=':',linewidth=1,label=r'$M=\pi X$')
ax.set_xlabel('Number M of retained forward coefficients')
ax.set_ylabel('Absolute error in the inverse')
ax.set_title(r'Near-least-term inversion at $X=10$')
ax.legend(fontsize=9); ax.grid(True,which='major',alpha=.22)
fig.tight_layout()
folder=Path(__file__).resolve().parents[1]/'figures'
fig.savefig(folder/'optimal_truncation.pdf')
fig.savefig(folder/'optimal_truncation.png',dpi=180)
