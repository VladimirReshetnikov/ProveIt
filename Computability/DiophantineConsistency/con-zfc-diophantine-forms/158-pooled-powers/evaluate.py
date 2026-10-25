"""Evaluate the fixed polynomial at one explicitly supplied integer tuple.

Python 3.10+ and the accompanying verify.py suffice. This evaluates a tuple;
it does not search for zeros or decide consistency.

Examples:
  python3 evaluate.py --values tuple.json
  python3 evaluate.py --values - --residuals < tuple.json
  python3 evaluate.py --equation path/to/equation.json --values tuple.json

The input is one JSON array containing exactly the declared number of
integers. Booleans, floating-point numbers, and numeric strings are rejected.
"""
from pathlib import Path
import argparse,json,sys
from verify import read,validate_equation,unique_object,nonfinite_json
ROOT=Path(__file__).resolve().parent

def evaluate(equation,values,include_residuals=False):
 validation=validate_equation(equation,'equation to evaluate')
 dimension=validation['declared_coordinates']
 if type(values) is not list:raise ValueError('values must be a JSON array')
 if len(values)!=dimension:raise ValueError('expected '+str(dimension)+' coordinates; received '+str(len(values)))
 for i,value in enumerate(values):
  if type(value) is not int:raise ValueError('coordinate '+str(i)+' must be an integer, not a Boolean, float, or string')
 residuals=[]
 for row in equation['residuals']:
  total=0
  for coefficient,monomial in row['terms']:
   term=coefficient
   for index in monomial:term*=values[index]
   total+=term
  residuals.append(total)
 value=sum(r*r for r in residuals)
 result={'dimension':dimension,'quadratic_residual_count':len(residuals),'polynomial_value':value,'is_zero':value==0,'nonzero_residual_count':sum(r!=0 for r in residuals)}
 if include_residuals:result['residual_values']=residuals
 return result

def main():
 if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
 ap=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
 ap.add_argument('--equation',type=Path,default=ROOT/'stages'/'principal225'/'equation.json')
 ap.add_argument('--values',required=True,help='JSON array file, or - to read from standard input')
 ap.add_argument('--residuals',action='store_true',help='include every individual residual value')
 ap.add_argument('--output',type=Path,help='write the result to this JSON file instead of stdout')
 args=ap.parse_args()
 try:
  equation=read(args.equation)
  text=sys.stdin.read() if args.values=='-' else Path(args.values).read_text()
  values=json.loads(text,object_pairs_hook=unique_object,parse_constant=nonfinite_json)
  result=evaluate(equation,values,args.residuals)
 except (OSError,ValueError,TypeError,KeyError) as exc:ap.error(str(exc))
 serialized=json.dumps(result,indent=2)+'\n'
 if args.output:args.output.write_text(serialized)
 else:sys.stdout.write(serialized)

if __name__=='__main__':main()
