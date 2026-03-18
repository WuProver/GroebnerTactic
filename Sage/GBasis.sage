# This is a file used for tactic `ideal_mem`
# input: Mvpolynomial set `S`
# output: Groebner Basis of `S`
import argparse
import re
import io
import sys
import json
import contextlib

from sage.all import PolynomialRing, QQ


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


def convert_gb_to_json(gb_list, vars_list):

    json_output = []

    for poly in gb_list:
        terms_list = []

        if poly.is_zero():
            terms_list.append({ "c": [int(0), int(1)], "e": [] })
        else:
            for exp_tuple, coeff in poly.dict().items():

                # --- Process Coefficient ---
                if hasattr(coeff, 'numerator') and hasattr(coeff, 'denominator'):
                    coeff_num = int(coeff.numerator())
                    coeff_den = int(coeff.denominator())
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

        # 2. Create Ring
        ring = create_polynomial_ring(vars_list)

        # 3. Parse Ideal Set (The Generators)
        cleaned_str = args.set.strip()
        if cleaned_str.startswith('[') and cleaned_str.endswith(']'):
            cleaned_str = cleaned_str[1:-1]

        if not cleaned_str.strip():
            poly_objs = []
        else:
            str_list = [s.strip() for s in cleaned_str.split(',') if s.strip()]
            poly_objs = [ring(s) for s in str_list]

        # 4. Compute Groebner Basis
        I = ring.ideal(poly_objs)
        gb = I.groebner_basis()
        # print(f"[DEBUG] {gb}")

        # 5. Convert GB to JSON
        json_result = convert_gb_to_json(gb, vars_list)

        # 6. Print Result
        print(json.dumps(json_result))

    except Exception as e:
        sys.stderr.write(f"[GBasis Error]: {e}\n")
        import traceback
        traceback.print_exc(file=sys.stderr)
        sys.exit(1)