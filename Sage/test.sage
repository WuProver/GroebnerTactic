from sage import *

def s_polynomial(f, g):
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

# 测试 x0 和 1-x2 的 S-多项式
# 定义多项式环，包含多个变量
R.<x0, x1, x2> = PolynomialRing(QQ, order='degrevlex')

# 定义多项式
f = x0
g = 1 - x2

print("多项式 f =", f)
print("多项式 g =", g)
print("f 的首项 =", f.lm())
print("f 的首项系数 =", f.lc())
print("g 的首项 =", g.lm())
print("g 的首项系数 =", g.lc())

# 计算 S-多项式
s_poly = s_polynomial(f, g)
print("\nS-多项式结果:")
print("s_polynomial(f, g) =", s_poly)
