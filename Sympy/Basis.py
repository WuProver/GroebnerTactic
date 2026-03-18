# This is a file used for tactic `basis`
# input : Mvpolynomial set `S = (f1,...fn)`
# output : The coeffs of the linear combination of (f_1,..,f_n) when expressing spoly(fi,fj)
import argparse
import re
import json
from itertools import product

from sympy import symbols, Poly, QQ
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
    ordered_vars.sort()
    return ordered_vars

def polynomial_division_multivariate(f, divisors, vars_symbols, domain):
    if not divisors:
        raise ValueError("divisors can not be Empty")
    for divisor in divisors:
        if divisor.is_zero:
            raise ValueError("divisor can not be 0")

    # Construct the zero polynomial
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

            # Check if leading monomial of divisor divides leading monomial of p
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

def s_polynomial(f, g, vars_symbols, domain):
    if f.is_zero or g.is_zero:
        return Poly(0, *vars_symbols, domain=domain)

    LM_f = f.LM()
    LM_g = g.LM()

    LC_f = f.LC()
    LC_g = g.LC()

    L_monomial = tuple(max(mf, mg) for mf, mg in zip(LM_f, LM_g))

    S_f_monom = tuple(lm - mf for lm, mf in zip(L_monomial, LM_f))
    S_g_monom = tuple(lm - mg for lm, mg in zip(L_monomial, LM_g))

    term1_multiplier = Poly({S_f_monom: LC_g}, *vars_symbols, domain=domain)
    term1 = term1_multiplier * f

    term2_multiplier = Poly({S_g_monom: LC_f}, *vars_symbols, domain=domain)
    term2 = term2_multiplier * g

    s_poly = term1 - term2
    return s_poly

def convert_quotient_to_json(quotients, vars_list):
    json_quotients = []

    for q_poly in quotients:
        terms_list = []

        if q_poly.is_zero:
            terms_list.append({
                "c": [int(0), int(1)],
                "e": []
            })
        else:
            # Poly.terms() returns tuples of (exponent_tuple, coefficient)
            for exp_tuple, coeff in q_poly.terms():
                if hasattr(coeff, 'numerator') and hasattr(coeff, 'denominator'):
                    coeff_num = int(coeff.numerator)
                    coeff_den = int(coeff.denominator)
                else:
                    coeff_num = int(coeff)
                    coeff_den = 1

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
        vars_list = extract_vars(args.set)

        if not vars_list:
            vars_list = ['x']

        vars_symbols = symbols(vars_list)
        if not isinstance(vars_symbols, (list, tuple)):
            vars_symbols = [vars_symbols]

        domain = QQ
        # order = 'lex'

        cleaned_str = args.set.strip().strip('[]')

        if not cleaned_str:
            set_list_str = []
        else:
            set_list_str = [s.strip() for s in cleaned_str.split(',') if s.strip()]

        # Parse string safely into SymPy expressions, transforming ^ to **
        transformations = standard_transformations + (implicit_multiplication_application, convert_xor)

        set_list = []
        for s in set_list_str:
            expr = parse_expr(s, transformations=transformations)
            poly = Poly(expr, *vars_symbols, domain=domain)
            set_list.append(poly)

        results = []

        for i, j in product(range(len(set_list)), repeat=2):
            f_i = set_list[i]
            f_j = set_list[j]

            s_poly = s_polynomial(f_i, f_j, vars_symbols, domain)

            if not set_list:
                continue

            quotients, remainder = polynomial_division_multivariate(s_poly, set_list, vars_symbols, domain)

            json_output = convert_quotient_to_json(quotients, vars_list)
            results.append(json_output)

        print(json.dumps(results))

    except Exception as e:
        print(f"\n[!!! Basis Error !!!] : {e}")
        import traceback
        traceback.print_exc()