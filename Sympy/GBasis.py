# This is a file used for tactic `ideal_mem`
# input: Mvpolynomial set `S`
# output: Groebner Basis of `S`
import argparse
import re
import sys
import json

from sympy import symbols, Poly, QQ, groebner
from sympy.parsing.sympy_parser import (
    parse_expr,
    standard_transformations,
    implicit_multiplication_application,
    convert_xor
)

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

def convert_gb_to_json(gb_list, vars_list):
    json_output = []

    for poly in gb_list:
        terms_list = []

        if poly.is_zero:
            terms_list.append({ "c": [int(0), int(1)], "e": [] })
        else:
            # Poly.terms() returns tuples of (exponent_tuple, coefficient)
            for exp_tuple, coeff in poly.terms():

                # --- Process Coefficient ---
                if hasattr(coeff, 'numerator') and hasattr(coeff, 'denominator'):
                    coeff_num = int(coeff.numerator)
                    coeff_den = int(coeff.denominator)
                else:
                    coeff_num = int(coeff)
                    coeff_den = 1

                # --- Process Exponents  ---
                exponent_pairs = []
                for i, power in enumerate(exp_tuple):
                    if power != 0:
                        var_name = vars_list[i]

                        match = re.search(r'_(\d+)$', var_name)
                        if match:
                            real_index = int(match.group(1))
                        else:
                            real_index = i

                        exponent_pairs.append([real_index, int(power)])

                exponent_pairs.sort(key=lambda x: x[0])

                terms_list.append({
                    "c": [coeff_num, coeff_den],
                    "e": exponent_pairs
                })

        json_output.append(terms_list)

    return json_output

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description = "Compute Groebner Basis and return its coefficients")
    parser.add_argument('-s', '--set', type = str, required=True, help="Polynomial set to compute GB for, e.g. '[x^2+y, y-1]'")
    args = parser.parse_args()

    try:
        # 1. Extract variables
        vars_list = extract_vars(args.set)

        if not vars_list:
            sys.stderr.write("[ERROR]: No variables found in input.\n")
            sys.exit(1)

        # 2. Create Symbols and Domain
        vars_symbols = symbols(vars_list)
        if not isinstance(vars_symbols, (list, tuple)):
            vars_symbols = [vars_symbols]

        domain = QQ

        # 3. Parse Ideal Set (The Generators)
        cleaned_str = args.set.strip()
        if cleaned_str.startswith('[') and cleaned_str.endswith(']'):
            cleaned_str = cleaned_str[1:-1]

        poly_objs = []
        if cleaned_str.strip():
            str_list = [s.strip() for s in cleaned_str.split(',') if s.strip()]

            # Setup parser transformations
            transformations = standard_transformations + (implicit_multiplication_application, convert_xor)

            for s in str_list:
                expr = parse_expr(s, transformations=transformations)
                poly_objs.append(Poly(expr, *vars_symbols, domain=domain))

        # 4. Compute Groebner Basis
        if not poly_objs:
            gb_polys = []
        else:
            # Compute GB and ensure the result is a list of Poly objects
            gb = groebner(poly_objs, *vars_symbols, domain=domain, order='lex')
            gb_polys = [Poly(p, *vars_symbols, domain=domain) for p in gb]

        # 5. Convert GB to JSON
        json_result = convert_gb_to_json(gb_polys, vars_list)

        # 6. Print Result
        print(json.dumps(json_result))

    except Exception as e:
        sys.stderr.write(f"[GBasis Error]: {e}\n")
        import traceback
        traceback.print_exc(file=sys.stderr)
        sys.exit(1)