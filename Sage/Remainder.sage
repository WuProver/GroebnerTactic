# This is a file used for tactic `remainder`
# Input : Mvpolynomial `f` and Mvpolynomial set `S`
# Output : The coeffs of the linear combination of `f` with respect to `S`
import argparse
import ast
import re
import io
import contextlib
import json

from sage.all import PolynomialRing, QQ, lcm
from fractions import Fraction


def extract_vars(poly_str, divisors_str):
    combined_str = poly_str + " " + divisors_str

    tokens = re.findall(r'[a-zA-Z_][a-zA-Z0-9_]*', combined_str)

    seen = set()
    ordered_vars = []
    for var in tokens:
        if var not in seen:
            seen.add(var)
            ordered_vars.append(var)
    
    ordered_vars.sort()

    return ordered_vars

def create_polynomial_ring(vars_list, order='lex', base_ring=QQ):

    if order not in ['lex', 'degrevlex', 'deglex']:
        raise ValueError(f"Unsupported order: {order}")

    R = PolynomialRing(base_ring, vars_list, order=order)
    return R

def polynomial_division_multivariate(f, divisors, ring):

    if not divisors:
      raise ValueError("divisors can not be Empty")

    for divisor in divisors:
      if divisor == 0:
        raise ValueError("divisor can not be 0")

    r = ring.zero()
    p = f
    quotients = [ring.zero() for _ in divisors]

    while p != 0:
        divided = False
        for i, divisor in enumerate(divisors):
            lt_p = p.lt()
            # print(f"[DEBUG] divisor: {divisor}")
            # print(f"[DEBUG] type: {type(divisor)}")
            divisor = ring(divisor)
            # print(f"[DEBUG] divisor': {divisor}")
            # print(f"[DEBUG] type': {type(divisor)}")
            lt_divisor = divisor.lt()
            # print(f"divisor leading term {lt_divisor}")

            if lt_p != 0 and lt_divisor.divides(lt_p):
                quotient_term = lt_p // lt_divisor
                quotients[i] += quotient_term
                p -= quotient_term * divisor
                divided = True
                break

        if not divided:
            lt_p = p.lt()
            r += lt_p
            p -= lt_p

    verification = r + sum(quotients[i] * ring(divisors[i]) for i in range(len(divisors)))
    if f == verification:
      return quotients, r
    else:
      raise ValueError("Verification of the result failed")

def s_polynomial(f, g):

    LT_f = f.lt()
    LT_g = g.lt()
    LC_f = LT_f.lc()
    LM_f = LT_f / LC_f
    LC_g = LT_g.lc()
    LM_g = LT_g / LC_g
    L = lcm(LT_f, LT_g)
    s_poly = (L / LM_f) * f * LC_g  - (L / LM_g) * g * LC_f
    return s_poly
    

def convert_quotient_to_json(quotients, vars_list):
    json_quotients = []
    num_vars = len(vars_list)
    
    var_to_index = {var: i for i, var in enumerate(vars_list)}

    for q_poly in quotients:
        terms_list = []
        
        # parse 0-polynomial
        if q_poly.is_zero():
            terms_list.append({
                "c": [int(0), int(1)], 
                "e": [] 
            })
        else:
            for exp_tuple, coeff in q_poly.dict().items():
                # process coefficient
                if coeff.parent() is QQ:
                    # process rational number
                    coeff_num = int(coeff.numerator())
                    coeff_den = int(coeff.denominator())
                elif coeff.is_integer():
                    # process int number
                    coeff_num = int(coeff)
                    coeff_den = 1
                else:
                    coeff_num = int(coeff)
                    coeff_den = 1

                
                # process exponent
                exponent_pairs = []

                if isinstance(exp_tuple, int):
                   
                    if exp_tuple == 0:
                        exp_list = [0] * num_vars
                    else:
                        exp_list = [exp_tuple]
                elif exp_tuple is None:
                    exp_list = []
                else:
                    exp_list = exp_tuple

                for i, power in enumerate(exp_list):
                    if power != 0:
                        exponent_pairs.append([i, int(power)])

                terms_list.append({
                    "c": [coeff_num, coeff_den],
                    "e": exponent_pairs
                })

        json_quotients.append(terms_list)

    return json_quotients



if __name__ == "__main__":
    parser = argparse.ArgumentParser(description = "remainder")

    parser.add_argument('-p', '--polynomial', type = str, required=True)

    parser.add_argument('-d', '--divisors', type = str, required=True)

    args = parser.parse_args()

    try:
        # Extract variables
        vars_list = extract_vars(args.polynomial, args.divisors)

        if not vars_list:
            vars_list = ['x']
            # raise ValueError("We can not find any variable in the input polynomial")

        # make the polynomial ring
        ring = create_polynomial_ring(vars_list)

        # make polynomial ring with variables
        with contextlib.redirect_stdout(io.StringIO()):
            # make polynomial ring with variables
            ring.inject_variables()

        # convert str to polynomial
        f = ring(args.polynomial)
        cleaned_str = args.divisors.strip().strip('[]')

        if not cleaned_str:
            divisors_list = []
        else:
            divisors_list = [s.strip() for s in cleaned_str.split(',') if s.strip()]

        # g = (((X_0^2 + X_1^3) + X_2^4) + X_3^5)

        # remainder algorithm
        quotients, remainder = polynomial_division_multivariate(f, divisors_list, ring)

        # print("\n--- Result ---")
        # print(f"Dividend (f): {f}")
        # print(f"Divisor (G):   {divisors_list}")
        # print(f"Quotient (q):     {quotients}")
        # print(f"Remainder (r):   {remainder}")
        # print("------------------------")
        json_output = convert_quotient_to_json(quotients, vars_list)
        # print(f"{json_output}")
        print(json.dumps(json_output))

    except Exception as e:
        print(f"\n[!!! Remainder Error !!!] : {e}")
        import traceback
        traceback.print_exc()
