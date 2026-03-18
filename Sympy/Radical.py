# This is a file used for tactic `radical_membership`
# input : polynomial `f` and the generator set of `I`
# output : `n` satisfies `f^n \in I`
import argparse
import re
import sys
from sympy import symbols, sympify
from sympy.polys.polytools import groebner, reduced

def extract_vars(combined_str):
    """
    Extract variables from input strings to ensure the Ring covers all symbols.
    """
    tokens = re.findall(r'[a-zA-Z_][a-zA-Z0-9_]*', combined_str)
    seen = set()
    ordered_vars = []
    for var in tokens:
        if var not in seen:
            seen.add(var)
            ordered_vars.append(var)
    return ordered_vars

def solve_radical(poly_str, set_str):
    all_text = poly_str + " " + set_str
    vars_list = extract_vars(all_text)

    if 't' not in vars_list:
        vars_list.append('t')
    else:
        raise ValueError(f"Your vars_list: {vars_list} contains `t`, you need to change the var added")
    if not vars_list:
        raise ValueError("No variables found in input.")

    # Create SymPy symbols
    syms = symbols(vars_list)
    t = syms[vars_list.index('t')]

    try:
        # Create a dictionary to map string variable names to SymPy symbol objects
        local_dict = {v.name: v for v in syms}
        f_expr = sympify(poly_str, locals=local_dict)
    except Exception:
        raise ValueError(f"Could not parse polynomial: {poly_str}")

    cleaned_set_str = set_str.strip()
    for char in ['{', '}', '[', ']']:
        cleaned_set_str = cleaned_set_str.replace(char, '')

    gens_expr = []
    if cleaned_set_str.strip():
        gen_strs = [s.strip() for s in cleaned_set_str.split(',') if s.strip()]
        gens_expr = [sympify(g, locals=local_dict) for g in gen_strs]

    # Rabinowitsch trick: I2 = <gens, 1 - t*f>
    B_list = list(gens_expr)
    B_list.append(1 - t * f_expr)

    # Compute Gröbner basis for I2 to check if 1 is in I2
    G2 = groebner(B_list, *syms, domain='QQ', order='lex')

    # Check if 1 is reducible by G2 to 0 (which means 1 is in I2)
    _, rem_1 = reduced(1, G2, *syms, domain='QQ', order='lex')

    if rem_1 == 0:
        # 1 is in I2. This implies f is in the radical of I1.
        # Since SymPy doesn't have a direct `lift` method to get the cofactors and max degree,
        # we check f^n \in I1 iteratively (guaranteed to terminate).

        G1 = groebner(gens_expr, *syms, domain='QQ', order='lex') if gens_expr else []

        n = 1
        f_pow_n = f_expr

        while True:
            if not G1:
                # If I1 is empty (zero ideal), f^n in I1 means f^n = 0
                if f_pow_n == 0:
                    return n
            else:
                # Check if f^n is in I1 by reducing it modulo the Gröbner basis G1
                _, rem_f = reduced(f_pow_n, G1, *syms, domain='QQ', order='lex')
                if rem_f == 0:
                    return n

            n += 1
            f_pow_n = f_pow_n * f_expr
    else:
        raise ValueError("The polynomial f is not in the radical of the ideal I.")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Find n such that f^n in Ideal, and return n.")

    parser.add_argument('-p', '--poly', type=str, required=True, help="Polynomial f")
    parser.add_argument('-s', '--set', type=str, required=True, help="Generators of Ideal")

    args = parser.parse_args()

    try:
        result = solve_radical(args.poly, args.set)
        print(result)

    except Exception as e:
        sys.stderr.write(f"\n[!!! Radical Error !!!] : {e}\n")
        sys.exit(1)