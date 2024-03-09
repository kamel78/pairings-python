
import libs.ExtensionFields as Extf
import libs.EllipticCurves as Ec
import libs.Arithmetics as Ar


_addG2Miller=lambda x1,y1,x2,y2:[(_1:=((_0:=((y2-y1)/(x2-x1)))**2-x2-x1)),(_2:=(_0*x2-y2))-_0*_1,_0,_2 ] # Used during pairings. The last two parameters are lamda and y-lamda*x
_doubleG2Miller=lambda x,y:[(_1:=((_0:=((3*x**2)/(2*y)))**2-2*x)),(_2:=(_0*x-y))-_0*_1,_0,_2]            # Used during pairings. The last two parameters are lamda and y-lamda*x 

# Bilinearity pairings engine for BLS 12 curves
# Implemented on M-Type Twist Model (With respect to curve's parametres included in "Parametres.py")
def BLS12PairingsEngine(params):
    class BLS12PairingsEngine :               
        def _miller_loop(P,Q):
            f = BLS12PairingsEngine.GT.one()._raw
            t = [Q.x,Q.y]
            _Py = Ar.invert(P.y,_basefield)        # using optimization trick from "Guide to pairings-based cryptography" section 11.2.1
            _Px = (-(P.x * _Py)) % _basefield  
            for i in _loop:                       
                f = [j % _basefield for j in Ar._sqrFp12(f)]
                t = _doubleG2Miller(t[0],t[1])  
                f = [j % _basefield for j in  Ar._sparse_mulFp12(f,(_Py * t[3])._raw + (_Px * t[2])._raw)]    
                if i != 0:
                    t = _addG2Miller(Q.x,i * Q.y,t[0],t[1])
                    f = [j % _basefield for j in  Ar._sparse_mulFp12(f,(_Py * t[3])._raw + (_Px*t[2])._raw)]                
            return BLS12PairingsEngine.GT(f)        
        def paire(P,Q):        return BLS12PairingsEngine._miller_loop(P,Q).final_exponentiation()
        def hashtoG1(id):      return BLS12PairingsEngine.G1.hashtoG1(id)
        def hashtoG2(id):      return BLS12PairingsEngine.G2.hashtoG2(id)
        def pickRandomG1():    return BLS12PairingsEngine.G1.pickTorsionPoint()
        def pickRandomG2():    return BLS12PairingsEngine.G2.pickTorsionPoint()
        def pickRandomScalar():return BLS12PairingsEngine.G1.pickRandomScalar()
    BLS12PairingsEngine.G1 = Ec.ECFP(params)
    BLS12PairingsEngine.G2 = Ec.ECFP2(params)
    BLS12PairingsEngine.GT = Extf.F12(params)
    _loop = Ar.bestrepr(abs(params["u"]),"down")[0][1:]
    _basefield = params["p"]
    return BLS12PairingsEngine

# Bilinearity pairings engine for BLS 24 curves
# Implemented on D-Type Twist Model (With respect to curve's parametres included in "Parametres.py")
def BLS24PairingsEngine(params):
    class BLS24PairingsEngine :               
        def _miller_loop(P,Q):
            f = BLS24PairingsEngine.GT.one()._raw
            t = [Q.x,Q.y]       
            _Py = Ar.invert(P.y,_basefield)
            _Px = (-(P.x * _Py)) % _basefield        
            for i in _loop:                       
                f = [j % _basefield for j in Ar._sqrFp24(f)]
                t = _doubleG2Miller(t[0],t[1])  
                f = [j % _basefield for j in Ar._sparseMulFp24(f,(_Py*t[3])._raw+(_Px *t[2])._raw )]    
                if i != 0:
                    t = _addG2Miller(Q.x,i * Q.y,t[0],t[1])
                    f = [j % _basefield for j in Ar._sparseMulFp24(f,(_Py*t[3])._raw+(_Px *t[2])._raw )]                
            return BLS24PairingsEngine.GT(f)        
        def paire(P,Q):        return BLS24PairingsEngine._miller_loop(P,Q).final_exponentiation()
        def hashtoG1(id):      return BLS24PairingsEngine.G1.hashtoG1(id)
        def hashtoG2(id):      return BLS24PairingsEngine.G2.hashtoG2(id)
        def pickRandomG1():    return BLS24PairingsEngine.G1.pickTorsionPoint()
        def pickRandomG2():    return BLS24PairingsEngine.G2.pickTorsionPoint()
        def pickRandomScalar():return BLS24PairingsEngine.G1.pickRandomScalar()
    BLS24PairingsEngine.G1 = Ec.ECFP(params)
    BLS24PairingsEngine.G2 = Ec.ECFP4(params)
    BLS24PairingsEngine.GT = Extf.F24(params)
    _loop = Ar.bestrepr(abs(params["u"]),"down")[0][1:]
    _basefield = params["p"]
    return BLS24PairingsEngine

# Bilinearity pairings engine for BLS 48 curves
# Implemented on M-Type Twist Model (With respect to curve's parametres included in "Parametres.py")
def BLS48PairingsEngine(params):
    class BLS48PairingsEngine :               
        def _miller_loop(P,Q):
            f = BLS48PairingsEngine.GT.one()._raw
            t = [Q.x,Q.y]
            _Py = Ar.invert(P.y,_basefield)        # using optimization trick from "Guide to pairings-based cryptography" section 11.2.1
            _Px = (-(P.x * _Py)) % _basefield  
            for i in _loop:                       
                f = [j % _basefield for j in Ar._sqrFp48(f)]
                t = _doubleG2Miller(t[0],t[1])  
                f = [j % _basefield for j in  Ar._sparseMulFp48(f,(_Py * t[3])._raw + (_Px * t[2])._raw)]    
                if i != 0:
                    t = _addG2Miller(Q.x,i * Q.y,t[0],t[1])
                    f = [j % _basefield for j in  Ar._sparseMulFp48(f,(_Py * t[3])._raw + (_Px * t[2])._raw)]                
            return BLS48PairingsEngine.GT(f)        
        def paire(P,Q):        return BLS48PairingsEngine._miller_loop(P,Q).final_exponentiation()
        def hashtoG1(id):      return BLS48PairingsEngine.G1.hashtoG1(id)
        def hashtoG2(id):      return BLS48PairingsEngine.G2.hashtoG2(id)
        def pickRandomG1():    return BLS48PairingsEngine.G1.pickTorsionPoint()
        def pickRandomG2():    return BLS48PairingsEngine.G2.pickTorsionPoint()
        def pickRandomScalar():return BLS48PairingsEngine.G1.pickRandomScalar()
    BLS48PairingsEngine.G1 = Ec.ECFP(params)
    BLS48PairingsEngine.G2 = Ec.ECFP8(params)
    BLS48PairingsEngine.GT = Extf.F48(params)
    _loop = Ar.bestrepr(abs(params["u"]),"down")[0][1:]
    _basefield = params["p"]
    return BLS48PairingsEngine
