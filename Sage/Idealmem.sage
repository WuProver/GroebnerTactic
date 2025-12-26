# This is a file used for tactic `ideal_mem`
# Input : Mvpolynomial `f` and Mvpolynomial set `S`(is not necessary a groebner basis)
# Output : the remainder coeff of `f` with respect to the groebner basis of `S`
# Example : sage Sage/Idealmem.sage -p "X_0" -s "[X_0, X_1]" -> []
import argparse
import ast
import re
import io
import contextlib
import json

from sage.all import PolynomialRing, QQ, lcm
from fractions import Fraction


def extract_vars(poly_str, divisors_str):
    combined_str = poly_str + divisors_str

    tokens = re.findall(r'[a-zA-Z_][a-zA-Z0-9_]*', combined_str)

    unique_vars = list(set(tokens))

    def natural_keys(text):
        return [int(c) if c.isdigit() else c for c in re.split(r'(\d+)', text)]

    unique_vars.sort(key=natural_keys)

    return unique_vars


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
    quotients = [ring.zero() for _ in divisors]

    while p != 0:
        divided = False
        for i, divisor in enumerate(divisors):
            lt_p = p.lt()
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

def convert_poly_to_json(poly, vars_list):
    terms_list = []
    
    ring_gens = poly.parent().gens()

    if poly.is_zero():
        terms_list.append({
            "c": [int(0), int(1)], 
            "e": [] 
        })
    else:
        for exp_tuple, coeff in poly.dict().items():

            if hasattr(coeff, 'numerator') and hasattr(coeff, 'denominator'):
                coeff_num = int(coeff.numerator())
                coeff_den = int(coeff.denominator())
            else:
                coeff_num = int(coeff)
                coeff_den = 1

            exponent_pairs = []
            
            for i, power in enumerate(exp_tuple):
                if power != 0:

                    current_var_obj = ring_gens[i]
                    var_name = str(current_var_obj)

                    match = re.search(r'_(\d+)$', var_name)
                    if match:
                        real_index = int(match.group(1))
                    else:
                        try:
                            real_index = vars_list.index(var_name)
                        except ValueError:
                             raise ValueError(f"Variable {var_name} not found.")

                    exponent_pairs.append([real_index, int(power)])

            exponent_pairs.sort(key=lambda x: x[0])

            terms_list.append({
                "c": [coeff_num, coeff_den],
                "e": exponent_pairs
            })

    return terms_list

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description = "ideal_mem")

    parser.add_argument('-p', '--polynomial', type = str, required=True)

    parser.add_argument('-s', '--set', type = str, required=True)

    args = parser.parse_args()

    try:
        # Extract variables
        vars_list = extract_vars(args.polynomial, args.set)

        if not vars_list:
            raise ValueError("We can not find any variable in the input polynomial")

        # make the polynomial ring
        ring = create_polynomial_ring(vars_list)

        # make polynomial ring with variables
        with contextlib.redirect_stdout(io.StringIO()):
            # make polynomial ring with variables
            ring.inject_variables()

        # convert str to polynomial
        f = ring(args.polynomial)
        cleaned_str = args.set.strip().strip('[]')

        if not cleaned_str:
            poly_objs = []
        else:
            poly_objs = [s.strip() for s in cleaned_str.split(',') if s.strip()]

        I = ring.ideal(poly_objs)

        try:
            coeffs = f.lift(I)
            
            output_list = []
            for c in coeffs:
                output_list.append(convert_poly_to_json(c, vars_list))
            
            print(json.dumps(output_list))

        except ValueError as e:
            sys.stderr.write(f"Polynomial is not in the ideal: {e}\n")
            print(json.dumps([])) 

    except Exception as e:
        sys.stderr.write(f"\n[!!! Coefficient Error !!!] : {e}\n")
        sys.exit(1)
