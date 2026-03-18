# This is a file used for tactic `ideal`
# Input : the generator list of ideal `I` and `J`
# Output : The coeffs of the linear combination of `f` in `I` with respect to `J` and the linear combination of `g` in `J` with respect to `I`
import re
import argparse
import json

from sympy import symbols, Poly, QQ, reduced
from sympy.parsing.sympy_parser import (
    parse_expr,
    standard_transformations,
    implicit_multiplication_application,
    convert_xor
)

def extract_vars(str1, str2):
    combined_str = str1 + " " + str2
    tokens = re.findall(r'[a-zA-Z_][a-zA-Z0-9_]*', combined_str)

    seen = set()
    ordered_vars = []
    for var in tokens:
        if var not in seen:
            seen.add(var)
            ordered_vars.append(var)

    def natural_keys(text):
       return [int(c) if c.isdigit() else c for c in re.split(r'(\d+)', text)]

    ordered_vars.sort(key=natural_keys)
    return ordered_vars

def parse_polynomials(vars_symbols, generator_list, domain):
    """
    Convert list of str to list of polynomial
    """
    parsed_polys = []
    transformations = standard_transformations + (implicit_multiplication_application, convert_xor)

    for poly_str in generator_list:
        try:
            expr = parse_expr(poly_str, transformations=transformations)
            poly = Poly(expr, *vars_symbols, domain=domain)
            parsed_polys.append(poly)
        except Exception as e:
            raise ValueError(f"Could not parse polynomial string '{poly_str}': {e}")
    return parsed_polys

def extended_buchberger(generators, vars_symbols, domain):
    """
    Computes the Groebner Basis and the transformation matrix C
    such that Basis[i] = sum(C[i][j] * generators[j])
    """
    basis = list(generators)
    zero = Poly(0, *vars_symbols, domain=domain)
    # C[i] maintains the linear combination representation of basis[i] in terms of original generators
    C = [[Poly(1, *vars_symbols, domain=domain) if i == j else zero for j in range(len(generators))] for i in range(len(generators))]

    pairs = [(i, j) for i in range(len(basis)) for j in range(i+1, len(basis))]

    while pairs:
        i, j = pairs.pop(0)
        p, q = basis[i], basis[j]

        if p.is_zero or q.is_zero:
            continue

        LM_p = p.LM()
        LM_q = q.LM()
        L_monom = tuple(max(m1, m2) for m1, m2 in zip(LM_p, LM_q))

        S_p_monom = tuple(l - m for l, m in zip(L_monom, LM_p))
        S_q_monom = tuple(l - m for l, m in zip(L_monom, LM_q))

        LC_p = p.LC()
        LC_q = q.LC()

        term_p = Poly({S_p_monom: LC_q}, *vars_symbols, domain=domain)
        term_q = Poly({S_q_monom: LC_p}, *vars_symbols, domain=domain)

        # Calculate S-polynomial and its corresponding tracking coefficients
        s_poly = term_p * p - term_q * q
        s_C = [term_p * C[i][k] - term_q * C[j][k] for k in range(len(generators))]

        if s_poly.is_zero:
            continue

        # Reduce the S-polynomial by the current basis
        quotients, remainder = reduced(s_poly, basis, *vars_symbols, domain=domain)

        if not remainder.is_zero:
            basis.append(remainder)
            rem_C = []
            for k in range(len(generators)):
                c_k = s_C[k]
                for idx, Q in enumerate(quotients):
                    if not Q.is_zero:
                        c_k -= Q * C[idx][k]
                rem_C.append(c_k)
            C.append(rem_C)

            new_idx = len(basis) - 1
            for k in range(new_idx):
                pairs.append((k, new_idx))

    return basis, C

def find_linear_representation(poly_list_to_represent, ideal_basis, vars_symbols, domain):
    results = []
    zero = Poly(0, *vars_symbols, domain=domain)

    if not ideal_basis:
        for poly in poly_list_to_represent:
            if poly.is_zero:
                results.append([])
            else:
                print(f"\n[Error In Find Representation] : Polynomial is not in the empty ideal")
        return results

    # Precompute the extended Groebner basis
    G, C = extended_buchberger(ideal_basis, vars_symbols, domain)

    for poly in poly_list_to_represent:
        try:
            # Step 1: Divide by the Groebner Basis
            quotients, remainder = reduced(poly, G, *vars_symbols, domain=domain)

            if not remainder.is_zero:
                # Mirroring Sage's behavior: Throw an exception if it's not in the ideal
                raise ValueError(f"Polynomial {poly} is not in the ideal")

            # Step 2: Remap coefficients through the transformation matrix C
            final_coeffs = [zero] * len(ideal_basis)
            for idx, Q in enumerate(quotients):
                if not Q.is_zero:
                    for k in range(len(ideal_basis)):
                        final_coeffs[k] += Q * C[idx][k]

            results.append(final_coeffs)

        except Exception as e:
            print(f"\n[Error In Find Representation] : {e}")
            import traceback
            traceback.print_exc()

    return results

def convert_polys_to_json(polys, vars_list):
    json_polys = []

    for q_poly in polys:
        terms_list = []

        # Parse 0-polynomial
        if q_poly.is_zero:
            terms_list.append({
                "c": [int(0), int(1)],
                "e": []
            })
        else:
            # Poly.terms() returns tuples of (exponent_tuple, coefficient)
            for exp_tuple, coeff in q_poly.terms():

                # Process coefficient
                if hasattr(coeff, 'numerator') and hasattr(coeff, 'denominator'):
                    coeff_num = int(coeff.numerator)
                    coeff_den = int(coeff.denominator)
                else:
                    coeff_num = int(coeff)
                    coeff_den = 1

                # Process exponents
                exponent_pairs = []
                for i, power in enumerate(exp_tuple):
                    if power != 0:
                        current_var_name = vars_list[i]

                        match = re.search(r'_(\d+)$', current_var_name)
                        if match:
                            real_index = int(match.group(1))
                        else:
                            try:
                                real_index = vars_list.index(current_var_name)
                            except ValueError:
                                real_index = i

                        exponent_pairs.append([real_index, int(power)])

                exponent_pairs.sort(key=lambda x: x[0])

                terms_list.append({
                    "c": [coeff_num, coeff_den],
                    "e": exponent_pairs
                })

        json_polys.append(terms_list)

    return json_polys

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description = "ideal")
    parser.add_argument('-I', '--generator1', type = str, required=True)
    parser.add_argument('-J', '--generator2', type = str, required=True)
    args = parser.parse_args()

    try:
        # Extract variables
        vars_list = extract_vars(args.generator1, args.generator2)

        if not vars_list:
            raise ValueError("We can not find any variable in the input polynomial")

        # Create SymPy symbols
        vars_symbols = symbols(vars_list)
        if not isinstance(vars_symbols, (list, tuple)):
            vars_symbols = [vars_symbols]

        domain = QQ

        # Convert str to polynomial list
        cleaned_str_1 = args.generator1.strip().strip('[]')
        cleaned_str_2 = args.generator2.strip().strip('[]')

        if not cleaned_str_1:
            generator_1 = []
        else:
            generator_1 = [s.strip() for s in cleaned_str_1.split(',') if s.strip()]

        if not cleaned_str_2:
            generator_2 = []
        else:
            generator_2 = [s.strip() for s in cleaned_str_2.split(',') if s.strip()]

        # Parse generating polynomials
        G1 = parse_polynomials(vars_symbols, generator_1, domain)
        G2 = parse_polynomials(vars_symbols, generator_2, domain)

        if not G1 or not G2:
            print("\n[!!! Warning !!!] One or both generator lists are empty. Cannot proceed with representation calculation.")
            print(json.dumps([[], []]))
        else:
            # Find representations
            results_G1_in_J = find_linear_representation(G1, G2, vars_symbols, domain)
            results_G2_in_I = find_linear_representation(G2, G1, vars_symbols, domain)

            json_result_1 = []
            for coeffs_list in results_G1_in_J:
                json_result_1.append(convert_polys_to_json(coeffs_list, vars_list))

            json_result_2 = []
            for coeffs_list in results_G2_in_I:
                json_result_2.append(convert_polys_to_json(coeffs_list, vars_list))

            result = []
            result.append(json_result_1)
            result.append(json_result_2)

            print(json.dumps(result))

    except Exception as e:
        print(f"\n[!!! Ideal Error !!!] : {e}")
        import traceback
        traceback.print_exc()