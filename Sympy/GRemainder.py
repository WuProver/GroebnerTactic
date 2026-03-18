# This is a file used for tactic `ideal_not_mem`
# Input : Mvpolynomial `f` and Mvpolynomial set `S`(is not necessary a groebner basis)
# Output : the remainder of `f` with respect to the groebner basis of `S`
# Example : python ideal_not_mem.py -p "1" -s "[X_0, X_1]" -> 1
import argparse
import re
import json

from sympy import symbols, Poly, QQ, groebner, reduced
from sympy.parsing.sympy_parser import (
    parse_expr,
    standard_transformations,
    implicit_multiplication_application,
    convert_xor
)

def extract_vars(poly_str, divisors_str):
    combined_str = poly_str + divisors_str
    tokens = re.findall(r'[a-zA-Z_][a-zA-Z0-9_]*', combined_str)
    unique_vars = list(set(tokens))

    def natural_keys(text):
        return [int(c) if c.isdigit() else c for c in re.split(r'(\d+)', text)]

    unique_vars.sort(key=natural_keys)
    return unique_vars

def polynomial_division_multivariate(f, divisors, vars_symbols, domain):
    if not divisors:
        raise ValueError("divisors can not be Empty")
    for divisor in divisors:
        if divisor.is_zero:
            raise ValueError("divisor can not be 0")

    zero_poly = Poly(0, *vars_symbols, domain=domain)
    r = zero_poly
    p = f
    quotients = [zero_poly for _ in divisors]

    while not p.is_zero:
        divided = False
        for i, divisor in enumerate(divisors):
            LM_p = p.LM()
            LC_p = p.LC()
            LM_d = divisor.LM()
            LC_d = divisor.LC()

            if all(md <= mp for md, mp in zip(LM_d, LM_p)):
                quotient_monom = tuple(mp - md for mp, md in zip(LM_p, LM_d))
                quotient_coeff = LC_p / LC_d

                quotient_term = Poly({quotient_monom: quotient_coeff}, *vars_symbols, domain=domain)

                quotients[i] += quotient_term
                p -= quotient_term * divisor
                divided = True
                break

        if not divided:
            LM_p = p.LM()
            LC_p = p.LC()
            lt_p_poly = Poly({LM_p: LC_p}, *vars_symbols, domain=domain)

            r += lt_p_poly
            p -= lt_p_poly

    verification = r + sum(quotients[i] * divisors[i] for i in range(len(divisors)))
    if f == verification:
        return quotients, r
    else:
        raise ValueError("Verification of the result failed")

def convert_poly_to_json(poly, vars_list):
    terms_list = []

    if poly.is_zero:
        terms_list.append({
            "c": [int(0), int(1)],
            "e": []
        })
    else:
        for exp_tuple, coeff in poly.terms():

            if hasattr(coeff, 'numerator') and hasattr(coeff, 'denominator'):
                coeff_num = int(coeff.numerator)
                coeff_den = int(coeff.denominator)
            else:
                coeff_num = int(coeff)
                coeff_den = 1

            exponent_pairs = []

            for i, power in enumerate(exp_tuple):
                if power != 0:
                    var_name = vars_list[i]

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
    parser = argparse.ArgumentParser(description = "remainder")
    parser.add_argument('-p', '--polynomial', type = str, required=True)
    parser.add_argument('-s', '--set', type = str, required=True)
    args = parser.parse_args()

    try:
        # Extract variables
        vars_list = extract_vars(args.polynomial, args.set)

        if not vars_list:
            raise ValueError("We can not find any variable in the input polynomial or set")

        # Create SymPy symbols
        vars_symbols = symbols(vars_list)
        if not isinstance(vars_symbols, (list, tuple)):
            vars_symbols = [vars_symbols]

        domain = QQ
        order = 'lex'

        # Parse f (the polynomial)
        transformations = standard_transformations + (implicit_multiplication_application, convert_xor)
        f_expr = parse_expr(args.polynomial, transformations=transformations)
        f = Poly(f_expr, *vars_symbols, domain=domain)

        # Parse S (the divisors set)
        cleaned_str = args.set.strip()
        if cleaned_str.startswith('[') and cleaned_str.endswith(']'):
            cleaned_str = cleaned_str[1:-1]

        if not cleaned_str.strip():
            poly_objs = []
        else:
            str_list = [s.strip() for s in cleaned_str.split(',') if s.strip()]
            poly_objs = [Poly(parse_expr(s, transformations=transformations), *vars_symbols, domain=domain) for s in str_list]

        if poly_objs:
            # Calculate Groebner basis first (equivalent to I.groebner_basis())
            gb = groebner(poly_objs, *vars_symbols, domain=domain, order=order)
            gb_polys = [Poly(p, *vars_symbols, domain=domain) for p in gb]

            # Compute remainder of f wrt the Groebner basis using `reduced`
            _, remainder_expr = reduced(f, gb_polys, *vars_symbols, domain=domain, order=order)
            remainder = Poly(remainder_expr, *vars_symbols, domain=domain)
        else:
            # If the set is empty, the remainder is just the polynomial itself
            remainder = f

        json_output = convert_poly_to_json(remainder, vars_list)
        print(json.dumps(json_output))

    except Exception as e:
        print(f"\n[!!! Remainder Error !!!] : {e}")
        import traceback
        traceback.print_exc()