# This is a file used for tactic `ideal_mem`
# Input : Mvpolynomial `f` and Mvpolynomial set `S`(is not necessary a groebner basis)
# Output : the remainder coeff of `f` with respect to the groebner basis of `S`
# Example : python ideal_mem.py -p "X_0" -s "[X_0, X_1]" -> []
import argparse
import re
import sys
import json

from sympy import symbols, Poly, QQ, reduced
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

        s_poly = term_p * p - term_q * q
        s_C = [term_p * C[i][k] - term_q * C[j][k] for k in range(len(generators))]

        if s_poly.is_zero:
            continue

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
    parser = argparse.ArgumentParser(description = "ideal_mem")
    parser.add_argument('-p', '--polynomial', type = str, required=True)
    parser.add_argument('-s', '--set', type = str, required=True)
    args = parser.parse_args()

    try:
        # Extract variables
        vars_list = extract_vars(args.polynomial, args.set)

        if not vars_list:
            raise ValueError("We can not find any variable in the input polynomial")

        # Create SymPy symbols
        vars_symbols = symbols(vars_list)
        if not isinstance(vars_symbols, (list, tuple)):
            vars_symbols = [vars_symbols]

        domain = QQ

        transformations = standard_transformations + (implicit_multiplication_application, convert_xor)

        # Parse polynomial f
        f_expr = parse_expr(args.polynomial, transformations=transformations)
        f = Poly(f_expr, *vars_symbols, domain=domain)

        # Parse set S
        cleaned_str = args.set.strip().strip('[]')
        if not cleaned_str:
            poly_objs = []
        else:
            str_list = [s.strip() for s in cleaned_str.split(',') if s.strip()]
            poly_objs = [Poly(parse_expr(s, transformations=transformations), *vars_symbols, domain=domain) for s in str_list]

        try:
            if not poly_objs:
                if f.is_zero:
                    print(json.dumps([]))
                else:
                    raise ValueError("Polynomial is not in the empty ideal")
            else:
                # 1. Get Groebner basis G and transition matrix C
                G, C = extended_buchberger(poly_objs, vars_symbols, domain)

                # 2. Divide f by Groebner basis G
                quotients, remainder = reduced(f, G, *vars_symbols, domain=domain)

                # 3. If remainder != 0, f is not in the ideal
                if not remainder.is_zero:
                    raise ValueError(f"Remainder is not zero: {remainder}")

                # 4. Map the quotients back to original generators via C (this replaces f.lift(I))
                zero = Poly(0, *vars_symbols, domain=domain)
                coeffs = [zero] * len(poly_objs)

                for idx, Q in enumerate(quotients):
                    if not Q.is_zero:
                        for k in range(len(poly_objs)):
                            coeffs[k] += Q * C[idx][k]

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