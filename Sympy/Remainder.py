# This is a file used for tactic `remainder`
# Input : polynomial `f` and polynomial set `S`
# Output : The coeffs of the linear combination of `f` with respect to `S`
import argparse
import re
import json

from sympy import symbols, sympify
from sympy.polys import Poly

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

def polynomial_division_multivariate(f, divisors, syms):
    if not divisors:
        raise ValueError("divisors can not be Empty")

    # Removed `order=order` from all Poly instantiations
    for divisor in divisors:
        if Poly(divisor, *syms, domain='QQ').is_zero:
            raise ValueError("divisor can not be 0")

    r = Poly(0, *syms, domain='QQ')
    p = Poly(f, *syms, domain='QQ')

    div_polys = [Poly(d, *syms, domain='QQ') for d in divisors]
    quotients = [Poly(0, *syms, domain='QQ') for _ in divisors]

    while not p.is_zero:
        divided = False
        p_terms = p.terms()
        if not p_terms:
            break
        p_LM, p_LC = p_terms[0] # LM is tuple of exponents, LC is coefficient

        for i, divisor in enumerate(div_polys):
            d_LM, d_LC = divisor.terms()[0]

            # Check if leading monomial of divisor divides leading monomial of p
            if all(pm >= dm for pm, dm in zip(p_LM, d_LM)):
                # Calculate quotient term: p_LM / d_LM and p_LC / d_LC
                q_monom = tuple(pm - dm for pm, dm in zip(p_LM, d_LM))
                q_coeff = p_LC / d_LC

                # Create the term as a Poly
                q_term = Poly.from_dict({q_monom: q_coeff}, *syms, domain='QQ')

                quotients[i] = quotients[i] + q_term
                p = p - q_term * divisor
                divided = True
                break

        if not divided:
            # Move the leading term of p to the remainder
            lt_term = Poly.from_dict({p_LM: p_LC}, *syms, domain='QQ')
            r = r + lt_term
            p = p - lt_term

    # Verification
    verification = r + sum(quotients[i] * div_polys[i] for i in range(len(divisors)))
    f_poly = Poly(f, *syms, domain='QQ')
    if f_poly == verification:
        return quotients, r
    else:
        raise ValueError("Verification of the result failed")

def s_polynomial(f, g, syms):
    f_poly = Poly(f, *syms, domain='QQ')
    g_poly = Poly(g, *syms, domain='QQ')

    if f_poly.is_zero or g_poly.is_zero:
        return Poly(0, *syms, domain='QQ')

    f_LM, f_LC = f_poly.terms()[0]
    g_LM, g_LC = g_poly.terms()[0]

    # LCM of leading monomials
    lcm_LM = tuple(max(fm, gm) for fm, gm in zip(f_LM, g_LM))

    # L / LM_f * LC_g
    mult_f_monom = tuple(lm - fm for lm, fm in zip(lcm_LM, f_LM))
    mult_f = Poly.from_dict({mult_f_monom: g_LC}, *syms, domain='QQ')

    # L / LM_g * LC_f
    mult_g_monom = tuple(lm - gm for lm, gm in zip(lcm_LM, g_LM))
    mult_g = Poly.from_dict({mult_g_monom: f_LC}, *syms, domain='QQ')

    s_poly = mult_f * f_poly - mult_g * g_poly
    return s_poly

def convert_quotient_to_json(quotients, vars_list):
    json_quotients = []

    for q_poly in quotients:
        terms_list = []

        if q_poly.is_zero:
            terms_list.append({
                "c": [0, 1],
                "e": []
            })
        else:
            # q_poly.as_dict() returns a dictionary of {(exponents_tuple): coefficient}
            for exp_tuple, coeff in q_poly.as_dict().items():

                # Extract Numerator and Denominator
                num, den = coeff.as_numer_denom()
                coeff_num = int(num)
                coeff_den = int(den)

                # Process exponents
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
    parser = argparse.ArgumentParser(description="remainder")
    parser.add_argument('-p', '--polynomial', type=str, required=True)
    parser.add_argument('-d', '--divisors', type=str, required=True)

    args = parser.parse_args()

    try:
        # Extract variables
        vars_list = extract_vars(args.polynomial, args.divisors)

        if not vars_list:
            vars_list = ['x']

        # Create SymPy symbols
        syms = symbols(vars_list)
        if not isinstance(syms, (list, tuple)):
            syms = [syms]

        # Convert str to polynomial expressions mapping variables correctly
        local_dict = {v.name: v for v in syms}
        f_expr = sympify(args.polynomial, locals=local_dict)

        cleaned_str = args.divisors.strip().strip('[]')
        if not cleaned_str:
            divisors_list = []
        else:
            divisors_list = [sympify(s.strip(), locals=local_dict) for s in cleaned_str.split(',') if s.strip()]

        # remainder algorithm
        quotients, remainder = polynomial_division_multivariate(f_expr, divisors_list, syms)

        json_output = convert_quotient_to_json(quotients, vars_list)
        print(json.dumps(json_output))

    except Exception as e:
        print(f"\n[!!! Remainder Error !!!] : {e}")
        import traceback
        traceback.print_exc()