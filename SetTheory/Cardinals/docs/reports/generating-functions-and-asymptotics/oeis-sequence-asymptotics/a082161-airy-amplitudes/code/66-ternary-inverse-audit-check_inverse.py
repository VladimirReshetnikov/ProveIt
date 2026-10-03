import json
import mpmath as mp
mp.mp.dps = 90
c = 3 * mp.root(3, 3) * mp.airyaizero(1)
C = mp.mpf('1.7')
rows=[]
for A in [mp.mpf(27)/4,mp.mpf(27)/2]:
    def h(n):
        return mp.log(C)+2*mp.loggamma(n+1)+n*mp.log(A)+c*mp.root(n,3)+mp.mpf(5)/3*mp.log(n)
    for p in [2,4,8,12,20]:
        m=mp.mpf(10)**p
        theta=mp.mpf('.37')
        x=m+theta
        L=(1-theta)*h(m)+theta*h(m+1)
        w=mp.lambertw(mp.sqrt(A)*L/(2*mp.e))
        n0=L/(2*w)
        D=2*(w+1)
        g=c*mp.root(n0,3)+mp.mpf(8)/3*mp.log(n0)+mp.log(2*mp.pi*C)
        nhat=n0-g/D
        actual_error=x-nhat
        predicted= c*c*n0**(-mp.mpf(1)/3)*(1/(3*D**2)-1/D**3)
        rows.append({'A':str(A),'x':str(x),'x_minus_approx':mp.nstr(actual_error,15),'log_scaled_error':mp.nstr(actual_error*mp.log(n0),15),'leading_error_ratio':mp.nstr(actual_error/predicted,15)})
print(json.dumps({'c':mp.nstr(c,30),'C':str(C),'scope':'Synthetic exact gamma model, log-linearly interpolated. This checks algebra, not the counting theorem.','rows':rows},indent=2))
