"""High-precision diagnostics only; no certified inverse or onset claims."""
import json
import mpmath as mp
from menage import fixed_count, circular_count, row_series


def evaluate(coefficients, value):
    return sum(mp.mpf(c.numerator)/c.denominator*value**j for j,c in enumerate(coefficients))


def log_model(x, s, order):
    if type(s) is not int or s < 1:
        raise ValueError("s must be a positive integer")
    if type(order) is not int or order < 0:
        raise ValueError("order must be a nonnegative integer")
    x = mp.mpf(x)
    if not mp.isfinite(x) or x <= max(2,order+1):
        raise ValueError("x must be finite and > max(2,order+1)")
    total=mp.mpf(1);fall=mp.mpf(1)
    for k in range(1,order+1):
        fall *= x-k
        total += (-1)**k/(mp.factorial(k)*fall)
    relative=evaluate(row_series(order,s),1/x)
    if total <= 0 or relative <= 0:
        raise ValueError("model factors must be positive")
    return -2+mp.loggamma(x+1)-mp.log(x-2)+mp.log(total)+mp.log(relative)


def main():
    records=[]
    with mp.workdps(100):
        for n in (50,100,200,400):
            for s in (1,2,3,4,5):
                a=fixed_count(n,s)
                ratio=mp.mpf((n-2)*a)/circular_count(n)
                rec={"n":n,"s":s,
                     "ratio_error_scaled_n11":mp.nstr(n**11*(ratio-evaluate(row_series(10,s),mp.mpf(1)/n)),30)}
                if s==4:
                    target=mp.log(a)
                    for order in (0,4,6,8,10):
                        root=mp.findroot(lambda t:log_model(t,s,order)-target,(n-mp.mpf(".2"),n+mp.mpf(".2")))
                        if not mp.isfinite(root):
                            raise RuntimeError("nonfinite diagnostic root")
                        rec["model_root_error_order_"+str(order)]=mp.nstr(root-n,30)
                    c=mp.log(2*mp.pi)/2-2
                    L=target-c;X=L/mp.lambertw(L/mp.e)
                    guess=X+mp.mpf(".5")-mp.mpf(23)/(24*X*mp.log(X))
                    rec["Lambert_error_scaled_X2logX"]=mp.nstr((n-guess)*X**2*mp.log(X),30)
                records.append(rec)
    print(json.dumps({"diagnostic_only":True,"precision_decimal_digits":100,
                      "certified_onset":None,"records":records},indent=2,sort_keys=True))

if __name__=="__main__":
    main()
