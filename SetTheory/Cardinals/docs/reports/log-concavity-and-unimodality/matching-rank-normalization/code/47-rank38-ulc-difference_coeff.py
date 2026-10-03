from population_coeff import *

def finite_differences(vals):
    ans=[]
    while vals:
        ans.append(vals[0])
        vals=[b-a for a,b in zip(vals,vals[1:])]
    return ans

