import gmpy2 as gmp
from libs.Parser import FieldsParser
import libs.Arithmetics as Ar
import libs.Frobinus as frob
import random

#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------#
## The Fp2 field Extension of the field Fp modulo the irriductibe polynomial u^2+Beta=0 
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------#
def F2(params):
  class F2:
    def __init__(x,a):
      if type(a) == str:x.fromstring(a)
      else:
        if (type(a) == list):x._setfromlist(a)
        else :raise TypeError(str(a)+" is an invalide inpute value for this field . ") 
    def __str__(x):return F2.parser.listtostring(x._raw,F2.tower,F2.tower)
    __repr__ = __str__
    def __eq__(x,y): 
      if (type(y) == int)or(type(y) == gmp.mpz):return (x._raw[1] == 0) & (x._raw[0] == y)
      else: return (x._raw == y._raw)
    def __ne__(x,y): 
      if (type(y) == int)or(type(y) == gmp.mpz):return ((x._raw[0]!=y)and(x._raw[1]==0))or((x._raw[1]!=0))
      else: return (x._raw != y._raw)
    def __add__(x,y):
      if (type(y) == int)or(type(y) == gmp.mpz):return F2([x._raw[0] + gmp.mpz(y) , x._raw[1]])
      else:return F2([x._raw[0] + y._raw[0] , x._raw[1] + y._raw[1]])
    def __sub__(x,y):
      if (type(y) == int)or(type(y) == gmp.mpz):return F2([x._raw[0] - gmp.mpz(y) , x._raw[1]])
      else: return F2([x._raw[0] - y._raw[0] , x._raw[1] - y._raw[1]])    
    def __mul__(x,y):
      if (type(y) == int)or(type(y) == gmp.mpz):return F2([y * x._raw[0], y * x._raw[1]])
      else: return F2( Ar._mulFp2(x._raw,y._raw))
    def sqr(x):return F2(Ar._sqrFp2(x._raw))
    def __rmul__(x,y):return F2([y * x._raw[0],y * x._raw[1]])
    def __mod__(x,y):return F2([x._raw[0] % y,x._raw[1] % y])
    def __neg__(x):return F2([-x._raw[0],-x._raw[1]])
    def __truediv__(x,y):return  x * y.inverse()
    def __rtruediv__(x,b):return b * x.inverse()
    def __pow__(x,b):
      if (type(b)!= int)and(type(b) != gmp.mpz):raise TypeError("Only integer powering is allowed in this field .")
      if b == 0:return F2([1,0])
      if x._raw[1] == 0:return F2([pow(x._raw[0],b),0])
      else :
        res=F2([1,0])
        for i in Ar.tobin(b):
            res = res.sqr()
            if i == 1:res = res * x
        return res
    def _setfromlist(x,list):
       if (type(list[0]) == int):x._raw = [gmp.mpz(list[0]) % _basefield ,gmp.mpz(list[1]) % _basefield]
       else:x._raw = [list[0] % _basefield,list[1] % _basefield]    # Only for internal use    
    def sqrt(x):
        _ = Ar._sqrtFp2(x._raw,_basefield,F2.inv2)
        return None if _ is None else F2(_)     
    def conjugate(x):return F2([x._raw[0],-x._raw[1]])    
    def inverse(x):return F2(Ar._invFp2(x._raw,_basefield))        
    def pickrandom():return F2([random.randint(0,_basefield-1),random.randint(0,_basefield - 1)])
    def tohex(x):return hex(x._raw[0]) + "+ u* " + hex(x._raw[1])
    def copy(x):return F2(x._raw)        
    def frobinus(x) :return F2([x._raw[0],-x._raw[1]])
    def fromstring(x,expr):x._setfromlist(x.parser.parse(expr))
    def isqr(x):return (_ := pow(x,((_basefield-1)//2))).frobinus() * _ == 1
    def tobytes(x):return Ar.tobytearray(x._raw,_basefield)
    def frombytes(x,bytearray):x._setfromlist(Ar.frombytearray(bytearray))
    def zero():return F2([0,0])
    def one():return F2([1,0])
    def u():return F2([0,1])
      
  if params["TargtedField"] !="Fp12" : raise TypeError("Invalid parametres for Fp2 field's construction...")
  _basefield = params["p"]
  F2.order   = _basefield
  F2.CurveParams = params
  F2.inv2  = params["inv2"]
  F2.inv2  = pow(gmp.mpz(2),-1,F2.order)
  F2.tower = [2]
  F2.parser = FieldsParser(F2.tower)
  return F2

#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------#
# Arithmetic computation over Fp12. Fp12 is the Twelvtic extention of Fp (Tower extention of order 2 for FP6)
# with respect to the irreductible polynômial W^2-Gamma=0. Elements are in the Form a+b*W (a and b are from Fp6).
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------#
def F12(params):
  class F12 :
      def __init__(self,a):
        if (type(a) == str):self.fromstring(a)
        else:
           if (type(a) == list):self._setfromlist(a)
           else :raise TypeError(str(a)+" is an invalide inpute value for this field . ") 
      def __str__(self):return F12.parser.listtostring(self._raw,F12.tower,F12.degrees)
      __repr__ = __str__
      def __eq__(x,y): 
        if (type(y) == int)or(type(y) == gmp.mpz):return (x._raw[1] == 0) & (x._raw[2] == 0) & (x._raw[3] == 0) & (x._raw[4] == 0)\
                                                         & (x._raw[5] == 0) & (x._raw[6] == 0) & (x._raw[7] == 0) & (x._raw[8] == 0)&\
                                                         (x._raw[9] == 0) & (x._raw[10] == 0) & (x._raw[11] == 0) & (x._raw[0] == y)
        else: return (x._raw == y._raw) 
      def __ne__(x,y): 
        if (type(y) == int) or (type(y) == gmp.mpz) : return (x._raw[0] != y) | (x._raw[1:] != [0,0,0,0,0,0,0,0,0,0,0])
        else: return (x._raw != y._raw)
      def __add__(x,y):
        if (type(y) == int) or (type(y) == gmp.mpz):return F12([x._raw[0] + y] + x._raw[1:])
        else: return F12([x._raw[0] + y._raw[0],x._raw[1] + y._raw[1],x._raw[2] + y._raw[2],x._raw[3] + y._raw[3],x._raw[4]\
                          + y._raw[4],x._raw[5] + y._raw[5],x._raw[6] + y._raw[6],x._raw[7] + y._raw[7],x._raw[8] + y._raw[8],\
                          x._raw[9] + y._raw[9],x._raw[10] + y._raw[10],x._raw[11] + y._raw[11]]) 
      def __sub__(x,y):
        if (type(y)==int)or(type(y)==gmp.mpz):return F12([x._raw[0]+y]+x._raw[1:])
        else: return F12([x._raw[0] - y._raw[0],x._raw[1] - y._raw[1],x._raw[2] - y._raw[2],x._raw[3] - y._raw[3],x._raw[4]\
                          - y._raw[4],x._raw[5] - y._raw[5],x._raw[6] - y._raw[6],x._raw[7] - y._raw[7],x._raw[8] - y._raw[8],\
                          x._raw[9] - y._raw[9],x._raw[10] - y._raw[10],x._raw[11] - y._raw[11]])    
      def __neg__(x):return F12([-x._raw[0],-x._raw[1],-x._raw[2],-x._raw[3],-x._raw[4],-x._raw[5],-x._raw[6],\
                                 -x._raw[7],-x._raw[8],-x._raw[9],-x._raw[10],-x._raw[11]])
      def __mul__(x,y):return F12(Ar._mulFp12(x._raw,y if (type(y) == int)or(type(y) == gmp.mpz) else y._raw) )       
      def __rmul__(x,y):
        if (type(y) == int)or(type(y) == gmp.mpz):return F12([y * x._raw[0],y * x._raw[1],y * x._raw[2],y * x._raw[3],y * x._raw[4],\
                                                              y * x._raw[5],y * x._raw[6],y * x._raw[7],y * x._raw[8],y * x._raw[9],\
                                                              y * x._raw[10],y * x._raw[11]])        
      def __mod__(x,y):return F12([x._raw[i] % y for i in range(12)])
      def sqr(self): return F12(Ar._sqrFp12(self._raw))     
      def unisqr(self):return F12(Ar._unisqrFp12(self._raw))
      def inverse(self):
        _0 = Ar._sqrFp6(self._raw[:6])
        _1 = Ar._sqrFp6(self._raw[6:])
        _ = [_0[0] - (_1[4] - _1[5]),_0[1] -(_1[4] + _1[5]),_0[2] - _1[0],_0[3] - _1[1],_0[4] - _1[2],_0[5] - _1[3]]
        t = Ar._invFp6(_,_basefield)
        return F12(Ar._mulFp6(self._raw[0:6],t) + Ar._mulFp6([-self._raw[6],-self._raw[7],-self._raw[8],-self._raw[9],-self._raw[10],-self._raw[11]],t))           
      def __truediv__(x,y):return  x * y.inverse()
      def __rtruediv__(self,b):return b * self.inverse()    
      def frobinus(self,order=1):        
        match order:
          case 1:return F12(frob.frobFp12(self._raw,fbc))                                                                                                  
          case 2:return F12(frob.frob2Fp12(self._raw,fbc))
          case 3:return F12(frob.frob3Fp12(self._raw,fbc)) 
      def conjugate(self):return F12([self._raw[0],self._raw[1],self._raw[2],self._raw[3],self._raw[4],self._raw[5],-self._raw[6],-self._raw[7],-self._raw[8],\
                                      -self._raw[9],-self._raw[10],-self._raw[11]])
      def pickrandom():return F12([random.randint(0,_basefield-1) for i in range(12)])
      def copy(self):return F12(self._raw)   
      def __pow__(x,b):
        if (type(b) != int)and(type(b) != gmp.mpz):raise TypeError("Only integer powering is allowed in this field .")
        if b == 0:return x.one()
        res = F12.one()
        for i in Ar.tobin(b):
            res = res.sqr()
            if i == 1:res = res * x
        if b < 0:return res.conjugate()
        else: return res      
      def cyclotomic_power(self,b):     # Efficient powering inside cyclotomic sub-group (x^(p^6+1)=1) -- Karabina Approache           
          expo = Ar.bestrepr(b)[0]
          match expo[0]:
            case 0:res = F12.one()
            case 1:res = self.copy()
            case -1:res = self.conjugate()
          tmp = self.copy()
          for i in expo[1:]:
            tmp = F12(Ar._sqrCompressFp12(tmp._raw))
            if i == 1:res = res*F12(Ar._sqrDecompressFp12(tmp._raw,_basefield))
            if i == -1:res = res*F12(Ar._sqrDecompressFp12(tmp._raw,_basefield)).conjugate()
          if b < 0:return res.conjugate()
          else :return res         
      def cyclotomic_power_scott(self,b):     # Efficient powering inside cyclotomic sub-group (x^(p^6+1)=1) -- Scott Approache           
          expo = Ar.bestrepr(b)[0]
          match expo[0]:
            case 0:res = F12.one()
            case 1:res = self.copy()
            case -1:res = self.conjugate()
          tmp = self.copy()
          for i in expo[1:]:
            tmp = F12(Ar._unisqrFp12(tmp._raw))
            if i==1:res=res*tmp
            if i==-1:res=res*tmp.conjugate()
          if b < 0:return res.conjugate()
          else :return res     
      def final_exponentiation(self):
          # It realy compute 3*(f^(p^12-1)/r) (the power of a pairings is a pairings)
          # Soft Part of the exponentiation :f^((p^6-1)*(p^2+1))
          #  Daiki Hayashida and Kenichiro Hayasaka and Tadanori Teruya https://eprint.iacr.org/2020/875.pdf
          t1 = self.conjugate()
          t2 = 1 / self
          self = (t1 * t2)
          t3 = self.frobinus(order=2)
          self = t3 * self          
          # Hard part of the Exponentiation  :f^(3*(p^4-p^2+1)/r) = f^((u-1)^2*(u+p)*(u^2+p^2-1)+3) 
          uu = _uparam - 1
          a = self.cyclotomic_power_scott(uu)
          a = a.cyclotomic_power_scott(uu)
          _ = a.frobinus()
          a = _ * a.cyclotomic_power_scott(_uparam)
          _ = a.frobinus(order = 2) * a.conjugate()
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = _ * a                     
          return (a * self) * self.unisqr()      
      def fromstring(x,expr):x._setfromlist(x.parser.parse(expr))        
      def tohex(self):return F12.parser.listtostring(self._raw,F12.tower,F12.degrees,format = "hex")
      def _setfromlist(x,list):
       if (type(list[0]) == int):x._raw = [gmp.mpz(list[i]) % _basefield for i in range(12)]
       else:x._raw = [list[i] % _basefield for i in range(12)]    # Only for internal use  
      def zero():return F12([0,0,0,0,0,0,0,0,0,0,0,0])
      def one():return F12([1,0,0,0,0,0,0,0,0,0,0,0])
      def u():return F12([0,1,0,0,0,0,0,0,0,0,0,0])
      def v():return F12([0,0,1,0,0,0,0,0,0,0,0,0])   
      def w():return F12([0,0,0,0,0,0,1,0,0,0,0,0])   
  
  if params["TargtedField"] !="Fp12" : raise TypeError("Invalid parametres for Fp12 field's construction...")
  _basefield = params["p"]
  _uparam = params["u"]
  F12.order = _basefield
  F12.tower = [2,3,2]
  F12.degrees = [2,6,12]
  F12.parser = FieldsParser(F12.tower)    
  F12.CurveParams = params
  fbc = params["frobConsts"]
  return F12

#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------#
## Arithmetic computation over Fp4 extension of the field Fp. Fp4 is  the quadratic extention of Fp2 (Tower extention of order 2 for FP2)
## with respect to the irreducible polynômial v²-u (v^2=u). Elements are on the form a+v.b (a,b from Fp2).
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------#
def F4(params):
  class F4:
      def __init__(x,a):
        if (type(a) == str):x.fromstring(a)
        else:
          if (type(a) == list):x._setfromlist(a)
          else :raise TypeError(str(a)+" is an invalide inpute value for this field . ") 
      def __str__(x):return F4.parser.listtostring(x._raw,F4.tower,F4.degrees)
      __repr__ = __str__
      def __eq__(x,y): 
       if (type(y) == int) or (type(y) == gmp.mpz):return (x._raw[1] == 0) & (x._raw[2] == 0) & (x._raw[3] == 0) & (x._raw[0] == y)
       else: return (x._raw == y._raw)
      def __ne__(x,y): 
       if (type(y) == int) or (type(y) == gmp.mpz) : return (x._raw[0] != y)|(x._raw[1:] != [0,0,0])
       else: return (x._raw != y._raw)
      def __add__(x,y):
        if (type(y) == int) or (type(y) == gmp.mpz):return F4([x._raw[0] + y]+x._raw[1:])
        else: return F4([x._raw[0] + y._raw[0],x._raw[1] + y._raw[1],x._raw[2] + y._raw[2],x._raw[3] + y._raw[3]])
      def __sub__(x,y):
        if (type(y) == int) or (type(y) == gmp.mpz): return F4([x._raw[0] - y] + x._raw[1:])
        else: return F4([x._raw[0] - y._raw[0],x._raw[1] - y._raw[1],x._raw[2] - y._raw[2],x._raw[3] - y._raw[3]])
      def __neg__(x):return F4([-x._raw[0],-x._raw[1],-x._raw[2],-x._raw[3]])
      def __mul__(x,y):return F4(Ar._mulFp4(x._raw,y if (type(y) == int)or(type(y) == gmp.mpz) else y._raw) )     
      def __rmul__(x,y):
        if (type(y) == int)or(type(y) == gmp.mpz):return F4([y * x._raw[i] for i in range(4)])
        else :return F4(Ar._mulFp4(y._raw + [0,0],x))
      def __mod__(x,y):return F4([x._raw[i] % y for i in range(4)])
      def sqr(x):return F4(Ar._sqrFp4(x._raw))         
      def sqrt(x):
         _ = Ar._sqrtFp4(x._raw,_basefield,F4.inv2)
         return None if _ is None else F4(_)           
      def inverse(x):return F4(Ar._invFp4(x._raw,_basefield))        
      def __truediv__(x,y):return  x * y.inverse()
      def __rtruediv__(x,b):return b * x.inverse()
      def __pow__(x,b):
        if (type(b) != int)and(type(b)!= gmp.mpz):raise TypeError("Only integer powering is allowed in this field .")
        if b == 0:return x.one()
        res = F4.one()
        for i in Ar.tobin(b):
            res = res.sqr()
            if i == 1:res = res * x
        return res     
      def _setfromlist(x,list):
       if (type(list[0]) == int):x._raw = [gmp.mpz(list[i]) % _basefield for i in range(4)]
       else:x._raw = [list[i] % _basefield for i in range(4)]    # Only for internal use    
      def frobinus(x):return F4(frob.frobFp4(x._raw,F4.frobinusconst))      
      def conjugate(x):return F4(Ar._conjugateFp4(x._raw))
      def pickrandom():return F4([random.randint(0,_basefield - 1) for i in range(4)])
      def copy(x):return F4(x._raw)
      def fromstring(x,expr):x._setfromlist(x.parser.parse(expr))
      def tobytes(x):return Ar.tobytearray(x._raw,_basefield)
      def tohex(self):return F4.parser.listtostring(self._raw,F4.tower,F4.degrees,format = "hex")
      def frombytes(x,bytearray):x._setfromlist(Ar.frombytearray(bytearray))       
      def isqr(x):return ((_1 := ((_ := pow(x,((_basefield - 1) // 2))).frobinus() * _)).frobinus().frobinus()) * _1 == 1
      def zero():return F4([0,0,0,0])
      def one():return F4([1,0,0,0])
      def u():return F4([0,1,0,0])
      def v():return F4([0,0,1,0])
  
  if params["TargtedField"] !="Fp24" : raise TypeError("Invalid parametres for Fp4 field's construction...")
  _basefield = params["p"]
  F4.frobinusconst = gmp.mpz(params["frobConsts"][0])
  F4.CurveParams = params
  F4.inv2 = gmp.mpz(params["inv2"])  
  F4.order = _basefield
  F4.tower = [2,2]
  F4.degrees = [2,4]
  F4.parser = FieldsParser(F4.tower)
  return F4

#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------#
# Arithmetic computation over Fp24 (finit field with primecaracteristiv p ). Fp24 is  the sextic
# extention of Fp4 (Tower extention of order 6 for FP4). With respect to the irreducible polynomial
# Z^3-Zetta=0  (Z^3=Zetta).  Elements Are in the form a+b*Z+c*Z^2, where a,b and c are from Fp8.
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------#
def F24(params):
  class F24 :
      def __init__(self,a):
        if (type(a) == str):self.fromstring(a)
        else:
           if (type(a) == list):self._setfromlist(a)
           else :raise TypeError(str(a) + " is an invalide inpute value for this field . ") 
      def __str__(self):return F24.parser.listtostring(self._raw,F24.tower,F24.degrees)
      __repr__ = __str__
      def __eq__(x,y): 
        if (type(y) == int) or (type(y) == gmp.mpz):return (x._raw[1:] == [0] * 23) & (x._raw[0] == y)
        else: return (x._raw == y._raw) 
      def __ne__(x,y): 
        if (type(y) == int) or (type(y) == gmp.mpz) : return (x._raw[0] != y) | (x._raw[1:] != [0] * 23)
        else: return (x._raw != y._raw)
      def __add__(x,y):
        if (type(y) == int) or (type(y) == gmp.mpz):return F24([x._raw[0] + y] + x._raw[1:])
        else: return F24([x._raw[0] + y._raw[0],x._raw[1] + y._raw[1],x._raw[2] + y._raw[2],x._raw[3] + y._raw[3],x._raw[4] + y._raw[4],x._raw[5] + \
                          y._raw[5],x._raw[6] + y._raw[6], x._raw[7] + y._raw[7],x._raw[8] + y._raw[8],x._raw[9] + y._raw[9],x._raw[10] + y._raw[10],\
                          x._raw[11] + y._raw[11],x._raw[12] + y._raw[12],x._raw[13] + y._raw[13],x._raw[14] + y._raw[14],x._raw[15] + y._raw[15],\
                          x._raw[16] + y._raw[16],x._raw[17] + y._raw[17],x._raw[18] + y._raw[18],x._raw[19] + y._raw[19],x._raw[20] + y._raw[20],\
                          x._raw[21] + y._raw[21],x._raw[22] + y._raw[22],x._raw[23] + y._raw[23]]) 
      def __sub__(x,y):
        if (type(y) == int) or (type(y) == gmp.mpz):return F24([x._raw[0] - y] + x._raw[1:])
        else: return F24([x._raw[0] - y._raw[0],x._raw[1] - y._raw[1],x._raw[2] - y._raw[2],x._raw[3] - y._raw[3],x._raw[4] - y._raw[4],x._raw[5] - y._raw[5],\
                          x._raw[6] - y._raw[6],x._raw[7] - y._raw[7],x._raw[8] - y._raw[8],x._raw[9] - y._raw[9],x._raw[10] - y._raw[10],x._raw[11] - y._raw[11],\
                          x._raw[12] - y._raw[12],x._raw[13] - y._raw[13],x._raw[14] - y._raw[14],x._raw[15] - y._raw[15],x._raw[16] - y._raw[16],x._raw[17] - \
                          y._raw[17],x._raw[18] - y._raw[18],x._raw[19] - y._raw[19],x._raw[20] - y._raw[20],x._raw[21] - y._raw[21],x._raw[22] - y._raw[22],\
                          x._raw[23] - y._raw[23]]) 
      def __neg__(x): return F24([-x._raw[0],-x._raw[1],-x._raw[2],-x._raw[3],-x._raw[4],-x._raw[5],-x._raw[6],-x._raw[7],-x._raw[8],-x._raw[9],-x._raw[10],-x._raw[11],\
                           -x._raw[12],-x._raw[13],-x._raw[14],-x._raw[15],-x._raw[16],-x._raw[17],-x._raw[18],-x._raw[19],-x._raw[20],-x._raw[21],-x._raw[22],-x._raw[23]])
      def __mod__(x,y):return F24([x._raw[i] % y for i in range(24)])
      def __mul__(x,y):return F24(Ar._mulFp24(x._raw,y if (type(y) == int)or(type(y) == gmp.mpz) else y._raw))           
      def __rmul__(x,y):
        if (type(y) == int)or(type(y) == gmp.mpz):return F24([y * x._raw[0],y * x._raw[1],y * x._raw[2],y * x._raw[3],y * x._raw[4],y * x._raw[5],y * x._raw[6],y * x._raw[7],\
                                                              y * x._raw[8],y * x._raw[9],y * x._raw[10],y * x._raw[11],y * x._raw[12],y * x._raw[13],y * x._raw[14],y * x._raw[15], \
                                                              y * x._raw[16],y * x._raw[17],y * x._raw[18],y * x._raw[19],y * x._raw[20],y * x._raw[21],y * x._raw[22],y * x._raw[23]])        
      def sqr(self):return F24(Ar._sqrFp24(self._raw))    
      def unisqr(self):return F24(Ar._unisqrFp24(self._raw))
      def inverse(self):return F24(Ar._invFp24(self._raw,_basefield))
      def __truediv__(x,y):return  x * y.inverse()
      def __rtruediv__(self,b):return b * self.inverse()  
      def conjugate(self):return F24([self._raw[0],self._raw[1],self._raw[2],self._raw[3],-self._raw[4],-self._raw[5],-self._raw[6],-self._raw[7],\
                                      -self._raw[8],-self._raw[9],-self._raw[10],-self._raw[11],self._raw[12],self._raw[13],self._raw[14],self._raw[15],\
                                      self._raw[16],self._raw[17],self._raw[18],self._raw[19],-self._raw[20],-self._raw[21],-self._raw[22],-self._raw[23]\
                                      ])
      def frobinus(self,order = 1):
        match order:
          case 1:return F24(frob.frobFp24(self._raw,fbc))            
          case 2:return F24(frob.frob2Fp24(self._raw,fbc))
          case 4:return F24(frob.frob4Fp24(self._raw,fbc))
      def pickrandom():return F24([random.randint(0,_basefield - 1) for i in range(24)])
      def copy(self):return F24(self._raw)   
      def fromstring(x,expr):x._setfromlist(x.parser.parse(expr))        
      def _setfromlist(x,list):
       if (type(list[0]) == int):x._raw = [gmp.mpz(list[i]) % _basefield for i in range(24)]
       else:x._raw = [list[i] % _basefield for i in range(24)]    # Only for internal use     
      def __pow__(x,b):
        if (type(b) != int) and (type(b) != gmp.mpz):raise TypeError("Only integer powering is allowed in this field .")
        if b == 0:return x.one()
        res = F24.one()
        for i in Ar.tobin(b):
            res = res.sqr()
            if i == 1:res = res * x
        if b < 0 :return res.conjugate()
        else :return res      
      def cyclotomic_power(self,b):     # Efficient powering inside cyclotomic sub-group (x^(p^12+1)=1) -- Karabina Approache  
        expo = Ar.bestrepr(b)[0]
        match expo[0]:
          case 0:res = F24.one()._raw
          case 1:res = self.copy()._raw
          case -1:res = self.conjugate()._raw
        tmp = self.copy()._raw
        for i in expo[1:]:
            tmp = [i % _basefield for i in Ar._sqrcompressFp24(tmp)]
            if i == 1:res = [i % _basefield for i in Ar._mulFp24(res,Ar._sqrdecompressFp24(tmp,_basefield))]
            if i == -1:res = [i % _basefield for i in Ar._mulFp24(res,Ar._conjugateFp24(Ar._sqrdecompressFp24(tmp,_basefield)))]
        if b < 0:return F24(Ar._conjugateFp24(res))
        else :return F24(res)    
      def cyclotomic_power_scott(self,b):     # Efficient powering inside cyclotomic sub-group (x^(p^12+1)=1) -- Scott Approache  
        expo = Ar.bestrepr(b)[0]
        match expo[0]:
          case 0:res = F24.one()._raw
          case 1:res = self.copy()._raw
          case -1:res = self.conjugate()._raw
        tmp = self.copy()._raw
        for i in expo[1:]:
            tmp = [i % _basefield for i in Ar._unisqrFp24(tmp)]
            if i == 1:res = [i % _basefield for i in Ar._mulFp24(res,tmp)]
            if i == -1:res = [i % _basefield for i in Ar._mulFp24(res,Ar._conjugateFp24(tmp))]
        if b < 0:return F24(Ar._conjugateFp24(res))
        else :return F24(res)
      
      def final_exponentiation(self):
          # It realy compute 3*(f^(p^24-1)/r) (the power of a pairings is a pairings)
          # Soft Part of the exponentiation :f^((p^12-1)*(p^4+1))
          #  Daiki Hayashida and Kenichiro Hayasaka and Tadanori Teruya https://eprint.iacr.org/2020/875.pdf
          t1 = self.conjugate()
          t2 = 1 / self
          self = (t1 * t2)
          t3 = self.frobinus(order=4)
          self = t3*self          
          # Hard part of the Exponentiation  :f^(3*(p^8-p^4+1)/r) = f^((u-1)^2*(u+p)*(u^2+p^2)*(u^4+p^4-1)+3) 
          uu = _uparam - 1
          a = self.cyclotomic_power_scott(uu)
          a = a.cyclotomic_power_scott(uu)
          _ = a.frobinus()
          a = _ * a.cyclotomic_power_scott(_uparam)
          _ = a.frobinus(order = 2)
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = _ * a           
          _ = a.frobinus(order = 4) * a.conjugate()
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = _ * a          
          return (a * self) * self.unisqr()
        
      def tohex(self):return F24.parser.listtostring(self._raw,F24.tower,F24.degrees,format="hex")
      def zero():return F24([0]*24)
      def one():return F24([1]+[0]*23)
      def u():return F24([0,1]+[0]*22)
      def v():return F24([0,0,1]+[0]*21)   
      def w():return F24([0,0,0,0,0,0,1]+[0]*17) 
      def z():return F24([0]*12+[1]+[0]*11)       

  if params["TargtedField"] !="Fp24" : raise TypeError("Invalid parametres for Fp24 field's construction...")
  _basefield = params["p"]
  _uparam = params["u"]
  F24.basefield = _basefield
  F24.order = _basefield
  F24.tower = [2,2,2,3]
  F24.degrees = [2,4,8,24]
  F24.parser = FieldsParser(F24.tower)
  F24.CurveParams = params
  fbc = params["frobConsts"]
  return F24

#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------#
# Arithmetic computation over Fp8. Fp8 is  the quadratic extention of Fp4 (Tower extention of order 2 for FP4)
# with respect to the polynomial W^2-Gamma=0 (W^2=Gamma). Elements are in the form a+b*W (a and b are from Fp4).
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------#
def F8(params):
  class F8:
      def __init__(self,a):
        if (type(a) == str):self.fromstring(a)
        else:
           if (type(a) == list):self._setfromlist(a)
           else :raise TypeError(str(a)+" is an invalide inpute value for this field . ") 
      def __str__(self):return F8.parser.listtostring(self._raw,F8.tower,F8.degrees)
      __repr__ = __str__
      def __eq__(x,y): 
        if (type(y) == int) or (type(y) == gmp.mpz):return (x._raw[1] == 0) & (x._raw[2] == 0) & (x._raw[3] == 0) & (x._raw[4] == 0) &\
                                                         (x._raw[5] == 0) & (x._raw[6] == 0) & (x._raw[7] == 0) & (x._raw[0] == y)
        else: return (x._raw == y._raw) 
      def __ne__(x,y): 
       if (type(y) == int) or (type(y) == gmp.mpz) : return (x._raw[0] != y) | (x._raw[1:] != [0,0,0,0,0,0,0])
       else: return (x._raw != y._raw)
      def __add__(x,y):
        if (type(y) == int) or (type(y) == gmp.mpz):return F8([x._raw[0] + y] + x._raw[1:])
        else: return F8([x._raw[0] + y._raw[0],x._raw[1] + y._raw[1],x._raw[2] + y._raw[2],x._raw[3] + y._raw[3],x._raw[4]\
                         + y._raw[4],x._raw[5] + y._raw[5],x._raw[6] + y._raw[6],x._raw[7] + y._raw[7]])  
      def __sub__(x,y):
        if (type(y) == int) or (type(y) == gmp.mpz):return F8([x._raw[0] - y] + x._raw[1:])
        else: return F8([x._raw[0] - y._raw[0],x._raw[1] - y._raw[1],x._raw[2] - y._raw[2],x._raw[3] - y._raw[3],x._raw[4]\
                         - y._raw[4],x._raw[5] - y._raw[5],x._raw[6] - y._raw[6],x._raw[7] - y._raw[7]])  
      def __neg__(x):return F8([-x._raw[0],-x._raw[1],-x._raw[2],-x._raw[3],-x._raw[4],-x._raw[5],-x._raw[6],-x._raw[7]])        
      def __mul__(x,y):  return F8(Ar._mulFp8(x._raw,y if (type(y) == int) or (type(y) == gmp.mpz) else y._raw) )     
      def __rmul__(x,y):
        if (type(y) == int)or(type(y) == gmp.mpz):
          return F8([y * x._raw[0],y * x._raw[1],y * x._raw[2],y * x._raw[3],y * x._raw[4],y * x._raw[5],y * x._raw[6],y * x._raw[7]])        
      def __mod__(x,y):return F8([x._raw[i] % y for i in range(8)])
      def sqr(self): return F8(Ar._sqrFp8(self._raw))              
      def inverse(self):return F8(Ar._invFp8(self._raw,_basefield))
      def __truediv__(x,y):return  x*y.inverse()
      def __rtruediv__(self,b):return b*self.inverse()
      def sqrt(self):
         _=Ar._sqrtFp8(self._raw,_basefield,F8.inv2)
         return None if _ is None else F8(_)           
      def frobinus(self):return F8(frob.frobFp8(self._raw,_frobConsts))
      def invfrobinus(self):return F8(frob.invfrobFp8(self._raw,_invFrobConsts))   # To be used for cofactor cleaning on BLS48
      def conjugate(self):return F8([self._raw[0],self._raw[1],self._raw[2],self._raw[3],-self._raw[4],-self._raw[5],-self._raw[6],-self._raw[7]])
      def pickrandom():return F8([random.randint(0,_basefield - 1) for i in range(8)])
      def copy(self):return F8(self._raw)
      def fromstring(x,expr):x._setfromlist(x.parser.parse(expr))        
      def _setfromlist(x,list):
       if (type(list[0]) == int):x._raw = [gmp.mpz(list[i]) % _basefield for i in range(8)]
       else:x._raw = [list[i] % _basefield for i in range(8)]    # Only for internal use  
      def __pow__(x,b):
        if (type(b) != int) and (type(b) != gmp.mpz):raise TypeError("Only integer powering is allowed in this field .")
        if b == 0:return F8([1,0,0,0,0,0,0,0])
        res = F8([1,0,0,0,0,0,0,0])
        for i in Ar.tobin(b):
            res=F8(Ar._sqrFp8(res._raw))
            if i == 1:
              res = F8(Ar._mulFp8(res._raw,x._raw))
        return res
      def zero():return F8([0,0,0,0,0,0,0,0])
      def one():return F8([1,0,0,0,0,0,0,0])
      def u():return F8([0,1,0,0,0,0,0,0])
      def v():return F8([0,0,1,0,0,0,0,0])    
      def w():return F8([0,0,0,0,1,0,0,0])

  if params["TargtedField"] !="Fp48" : raise TypeError("Invalid parametres for Fp8 field's construction...")   
  _basefield = gmp.mpz(params["p"])
  F8.CurveParams = params
  _frobConsts = F8.CurveParams["frobConsts"]
  _invFrobConsts = [gmp.invert(2*_frobConsts[0],_basefield),gmp.invert(_frobConsts[2],_basefield),gmp.invert(_frobConsts[1],_basefield)]
  F8.order = params["p"]
  F8.inv2 = gmp.invert(2 ,_basefield) 
  F8.tower = [2,2,2]
  F8.degrees = [2,4,8]
  F8.basefield = _basefield
  F8.tower = [2,2,2]
  F8.parser = FieldsParser(F8.tower)  
  return F8
                      
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------#
# Arithmetic computation over Fp48. Fp48 is the 48's degree extention of Fp (Tower extention of order 2 for FP24)
# with respect to the irreductible polynômial t^2-lamda=0. Elements are in the Form a+b*W (a and b are from Fp24).
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------#
def F48(params):
  class F48 :
      def __init__(self,a):
        if (type(a) == str):self.fromstring(a)
        else:
           if (type(a) == list):self._setfromlist(a)
           else :raise TypeError(str(a) + " is an invalide inpute value for this field . ") 
      def __str__(self):return F48.parser.listtostring(self._raw,F48.tower,F48.degrees)
      __repr__ = __str__
      def __eq__(x,y): 
        if (type(y) == int) or (type(y) == gmp.mpz):return (x._raw[1:] == [0] * 47) & (x._raw[0] == y)
        else: return (x._raw == y._raw) 
      def __ne__(x,y): 
        if (type(y) == int) or (type(y) == gmp.mpz) : return (x._raw[0] != y) | (x._raw[1:] != [0] * 47)
        else: return (x._raw != y._raw)
      def __add__(x,y):
        if (type(y) == int) or (type(y) == gmp.mpz):return F48([x._raw[0] + y] + x._raw[1:])
        else: return F48([x._raw[i] + y._raw[i] for i in range(48)])
      def __sub__(x,y):
        if (type(y) == int) or (type(y) == gmp.mpz):return F48([x._raw[0] - y] + x._raw[1:])
        else: return F48([x._raw[i] - y._raw[i] for i in range(48)])
      def __neg__(x):return F48([-x._raw[i] for i in range(48)])
      def __mul__(x,y):  return F48(Ar._mulFp48(x._raw,y._raw))
      def __rmul__(x,y):
         if type(y) == int:return F48([y * x._raw[i] for i in range(48)])
      def __mod__(x,y):return F48([x._raw[i] % y for i in range(48)])
      def sqr(self): return F48(Ar._sqrFp48(self._raw))
      def unisqr(self):return F48(Ar._unisqrFp48(self._raw))
      def inverse(self):return F48(Ar._invFp48(self._raw,_basefield))
      def __truediv__(x,y):return  x * y.inverse()
      def __rtruediv__(self,b):return b * self.inverse()
      def __pow__(x,b):
        if (type(b) != int) and (type(b) != gmp.mpz):raise TypeError("Only integer powering is allowed in this field .")
        if b == 0:return x.one()
        res = F48.one()
        for i in Ar.tobin(b):
            res = res.sqr()
            if i == 1:res = res * x
        if b < 0 :return res.conjugate()
        else :return res    
      def frobinus(self,order = 1):
        match order:
          case 1:return F48(frob.frobFp48(self._raw,F48._frob24))
          case 2:return F48(frob.frob2Fp48(self._raw,F48._frob24))
          case 4:return F48(frob.frob4Fp48(self._raw,F48._frob24))
          case 8:return F48(frob.frob8Fp48(self._raw,F48._frob24))
          case 24:return self.conjugate()
             
      def conjugate(self):return F48(Ar._conjugateFp48(self._raw))
      def pickrandom():return F48([random.randint(0,_basefield - 1) for i in range(48)])
      def copy(self):return F48(self._raw)   
      def fromstring(x,expr):x._setfromlist(x.parser.parse(expr))        
      def _setfromlist(x,list):
        if (type(list[0]) == int):x._raw = [gmp.mpz(list[i]) % _basefield for i in range(48)]
        else:x._raw = [list[i] % _basefield for i in range(48)]    # Only for internal use  
      
      def cyclotomic_power(self,b):     # Efficient powering inside cyclotomic sub-group (x^(p^24+1)=1) -- Karabina Approache         
          expo= Ar.bestrepr(b)[0]
          match expo[0]:
            case 0:res = F48.one()
            case 1:res = self.copy()
            case -1:res = self.conjugate()
          tmp = self.copy()
          for i in expo[1:]:
            tmp = F48(Ar._sqrcompressFp48(tmp._raw))
            if i == 1:res=res*F48(Ar._sqrdecompressFp48(tmp._raw,_basefield))
            if i == -1:res=res*F48(Ar._sqrdecompressFp48(tmp._raw,_basefield)).conjugate()
          if b < 0:return res.conjugate()
          else :return res   

      def cyclotomic_power_scott(self,b):     # Efficient powering inside cyclotomic sub-group (x^(p^24+1)=1) -- Scott Approache  
        expo = Ar.bestrepr(b)[0]
        match expo[0]:
          case 0:res = F48.one()._raw
          case 1:res = self.copy()._raw
          case -1:res = self.conjugate()._raw
        tmp = self.copy()._raw
        for i in expo[1:]:
            tmp = [i % _basefield for i in Ar._unisqrFp48(tmp)]
            if i == 1:res = [i % _basefield for i in Ar._mulFp48(res,tmp)]
            if i == -1:res = [i % _basefield for i in Ar._mulFp48(res,Ar._conjugateFp48(tmp))]
        if b < 0:return F48(Ar._conjugateFp48(res))
        else :return F48(res)

      def final_exponentiation(self):
          # It realy compute 3*(f^(p^48-1)/r) (the power of a pairings is a pairings)
          # Soft Part of the exponentiation :f^((p^24-1)*(p^8+1))
          # Daiki Hayashida and Kenichiro Hayasaka and Tadanori Teruya https://eprint.iacr.org/2020/875.pdf
          t1 = self.conjugate()
          t2 = 1 / self
          self = (t1 * t2)
          t3 = self.frobinus(order=8)
          self = t3*self          
          # Hard part of the Exponentiation  :f^(3*(p^16-p^8+1)/r) = f^((u-1)^2*(u+p)*(u^2+p^2)*(u^4+p^4)*(u^8+p^8-1)+3) 
          uu = _uparam - 1
          a = self.cyclotomic_power_scott(uu)
          a = a.cyclotomic_power_scott(uu)
          _ = a.frobinus()
          a = _* a.cyclotomic_power_scott(_uparam)
          _ = a.frobinus(order = 2)
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = _ * a           
          _ = a.frobinus(order = 4)
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = _ * a        
          _ = a.frobinus(order = 8) * a.conjugate()
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = a.cyclotomic_power_scott(_uparam)
          a = _ * a
          return (a * self) * self.unisqr()          
      def zero():return F48([0]*48)
      def one():return F48([1] + [0] * 47)
      def u():return F48([0,1] + [0] * 46)
      def v():return F48([0,0,1] + [0] * 45)   
      def w():return F48([0,0,0,0,0,0,1] + [0] * 41) 
      def z():return F48([0] * 12 + [1] + [0] * 35)     
      def t():return F48([0] * 24 + [1] + [0] * 23)    

  if params["TargtedField"] !="Fp48" : raise TypeError("Invalid parametres for Fp8 field's construction...")   
  _basefield = params["p"]
  _uparam = params["u"]
  F48.order = _basefield
  F48.tower = [2,2,2,3,2]
  F48.degrees = [2,4,8,24,48]
  F48.parser = FieldsParser(F48.tower)
  F48._frob24 = params["frobConsts"]
  F48.CurveParams = params
  return F48