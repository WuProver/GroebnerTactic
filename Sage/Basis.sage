# This is a file used for tactic `basis`
# input : Mvpolynomial set `S = (f1,...fn)`
# output : The coeffs of the linear combination of (f_1,..,f_n) when expressing spoly(fi,fj)
import argparse
import ast
import re
import io
import contextlib
import json

from sage.all import PolynomialRing, QQ, lcm
from fractions import Fraction
from itertools import combinations, product

def extract_vars(set_str):
    tokens = re.findall(r'[a-zA-Z_][a-zA-Z0-9_]*', set_str)
    
    seen = set()
    ordered_vars = []
    for var in tokens:
        if var not in seen:
            seen.add(var)
            ordered_vars.append(var)
    
    # add order sort
    ordered_vars.sort() 
    
    return ordered_vars

def create_polynomial_ring(vars_list, order='lex', base_ring=QQ):

    if order not in ['lex', 'degrevlex', 'deglex']:
        raise ValueError(f"Unsupported order: {order}")

    # R = PolynomialRing(base_ring, vars_list, order=order)
    R = PolynomialRing(base_ring, vars_list, order=order, implementation="singular")
    return R

def polynomial_division_multivariate(f, divisors, ring):

    if not divisors:
      raise ValueError("divisors can not be Empty")

    for divisor in divisors:
      if divisor == 0:
        raise ValueError("divisor can not be 0")

    r = ring.zero()
    p = f
    # print(f"[DEBUG] {f}")
    # print(f"[DEBUG] {type(f)}")
    quotients = [ring.zero() for _ in divisors]

    while p != 0:
        divided = False
        for i, divisor in enumerate(divisors):
            # print(f"[DEBUG] : {divisor}")
            # print(f"[DEBUG] : {type(divisor)}")
            lt_p = p.lt()
            # print(f"[DEBUG] divisor: {divisor}")
            # print(f"[DEBUG] type: {type(divisor)}")
            divisor = ring(divisor)
            # print(f"[DEBUG] divisor': {divisor}")
            # print(f"[DEBUG] type': {type(divisor)}")
            lt_divisor = divisor.lt()
            # print(f"divisor leading term {lt_divisor}")

            if lt_p != 0 and lt_divisor.divides(lt_p):
                quotient_term = lt_p / lt_divisor
                if not isinstance(quotient_term, ring.element_class):
                    quotient_term = ring(quotient_term)
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

    if f == 0 or g == 0:
        return 0

    LM_f = f.lm() 
    LM_g = g.lm()
    
    LC_f = f.lc()
    LC_g = g.lc()
    
    L_monomial = lcm(LM_f, LM_g)
    
    S_f = L_monomial // LM_f 
    S_g = L_monomial // LM_g
    
    term1 = (S_f * LC_g) * f
    term2 = (S_g * LC_f) * g
    
    s_poly = term1 - term2
    
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
                for i, power in enumerate(exp_tuple):
                    if power != 0:
                        exponent_pairs.append([i, int(power)])

                terms_list.append({
                    "c": [coeff_num, coeff_den],
                    "e": exponent_pairs
                })

        json_quotients.append(terms_list)

    return json_quotients

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description = "basis")

    parser.add_argument('-s', '--set', type = str, required=True)

    args = parser.parse_args()

    try:
        # Extract variables
        vars_list = extract_vars(args.set)

        if not vars_list:
            vars_list = ['x']
            # raise ValueError("We can not find any variable in the input polynomial")

        # make the polynomial ring
        ring = create_polynomial_ring(vars_list)

        # make polynomial ring with variables
        with contextlib.redirect_stdout(io.StringIO()):
            # make polynomial ring with variables
            ring.inject_variables()
        
        # convert set to polynomial set
        cleaned_str = args.set.strip().strip('[]')

        if not cleaned_str:
            set_list = []
        else:
            set_list = [s.strip() for s in cleaned_str.split(',') if s.strip()]
        

        results = []
        var_to_index = {var: i for i, var in enumerate(vars_list)}
        
        for i, j in product(range(len(set_list)), repeat=2):   
            # print(f"[DEBUG] i: {i}")
            # print(f"[DEBUG] j: {j}")
            f_i = set_list[i]
            f_j = set_list[j]

            f_i = ring(f_i)
            f_j = ring(f_j)
            
            s_poly = s_polynomial(f_i, f_j)
            # print(f"[SPoly]\n{s_poly}")
            quotients, remainder = polynomial_division_multivariate(s_poly, set_list, ring)
            # print(f"[f_i]\n {f_i}\n")
            # print(f"[f_j]\n {f_j}\n")
            # print(f"[QUOTIENTS]\n {quotients}")
            # print(f"[REMAINDER]\n {quotients}")
            json_output = convert_quotient_to_json(quotients, vars_list)

            results.append(json_output)
      
        print(json.dumps(results))
    except Exception as e:
        print(f"\n[!!! Basis Error !!!] : {e}")
        import traceback
        traceback.print_exc()