from sage import *


P = PolynomialRing(QQ,["x","y","z"],order="lex")
x, y, z = P.gens()

I = P.ideal(x^2-2*x*z+5, y*z^3+x*y^2, -8*z^3+3*y^2)
f = -18*x*y^5*z-96*x*y^4*z^2+9*x*y^4-592*x*y^3*z+45*y^5+240*y^4*z+320*x*y^2+1600*y^3

H = (-18*x*y^5*z-96*x*y^4*z^2+9*x*y^4-592*x*y^3*z+45*y^5+240*y^4*z+320*x*y^2+1600*y^3).lift(I)