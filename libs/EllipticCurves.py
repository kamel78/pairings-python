import gmpy2 as gmp
import random
import base64
import libs.Arithmetics as Ar
from libs.Tools import HashToField,Fpsgn0,I2OSP,OS2IP,FpMsgn0
import libs.ExtensionFields as Extf
import libs.Recorders as Recs

#--------------------------------------------------------------------------------------------------------------------------------------------------------------------#
# Elliptic Curves implementation Over Fp (for BLS12-24-48):
#                  - Affine coordinates implementation (field inversion is sufficently fast on gmp) 
#                  - SWU points mapping using isogenies
#                  - GLV Multuplication for Torsion points in G1
#                  - Sliding window multiplication for points not in G1 (in E(Fp1))
#                  - Constant-time implementation
#--------------------------------------------------------------------------------------------------------------------------------------------------------------------#
def ECFP(CurveParams):
   _addMixed = lambda _x,_y,_z,xx,yy:[xx,yy,1]if _z==0 else [((_2:=xx*_z-_x)*(_6:=((_1:=yy*_z-_y)**2)*_z-(_4:=_2*(_3:=_2**2))-2*(_5:=_3*_x)))% _basefield,(_1*(_5-_6)-_4*_y)% _basefield,(_4*_z)% _basefield]
   _addAffine     = lambda _x,_y,xx,yy:[(_1:=((_0:=((_y-yy)*gmp.invert((_x-xx),_basefield)))**2-_x-xx) % _basefield),(_0*(_x-_1)-_y) % _basefield]
   _doubleProjective = lambda _x,_y,_z:[_x,_y,_z]if _z==0 else [((_6:=(_1:=3*(_0:=_x**2))**2-((_5:=(_x+(_3:=_y*(_2:=(_y*_z<<1))))**2-_0-(_4:=_3**2))<<1))*_2) % _basefield,(_1*(_5-_6)-2*_4)% _basefield,(_2*_2**2)% _basefield]
   _doubleAffine     = lambda _x,_y:[(_1:=((_0:=((3*_x**2)*gmp.invert((_y<<1),_basefield)))**2-2*_x) % _basefield),(_0*(_x-_1)-_y)% _basefield]
     
   def _swumapping(u):
      #     Simplified Shallue-van de Woestijne-Ulas Method (Simplified SWU for AB == 0)
      #     https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-05#section-6.6.3
      #     https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-05#appendix-C.2
      t1 = (_swuZ * u**2) % _basefield
      t2 = t1**2 % _basefield
      x1 = (gmp.invert(t1 + t2,_basefield))
      if x1==0 : x1 = _invZ
      else :x1 = (x1 + 1) % _basefield
      x1  = (x1 * _BdivA) % _basefield
      gx1 = ((x1**2 + _swuA) * x1 + _swuB) % _basefield
      y   = Ar.rsqrt(gx1, _basefield)
      if (y != None):
         if Fpsgn0(u, _basefield) != Fpsgn0(y, _basefield): y = -y % _basefield
         x = x1
      else:
         x2  = (t1 * x1) % _basefield
         t2  = (t1 * t2) % _basefield
         gx2 = (gx1 * t2) % _basefield
         y   = Ar.rsqrt(gx2, _basefield)
         if Fpsgn0(u, _basefield) != Fpsgn0(y, _basefield): y = -y % _basefield
         x=x2
      # isogeny map from E' to E "Wahby and Boneh" https://eprint.iacr.org/2019/403
      x_num, x_den, y_num, y_den = _Xnum[0], _Xden[0], _Ynum[0], _Yden[0]
      powx = x
      for i in range(1,len(_Ynum)):
         y_num = (y_num + _Ynum[i]*powx) % _basefield
         y_den = (y_den + _Yden[i]*powx) % _basefield
         if i<len(_Xnum):
            x_num = (x_num + (_Xnum[i] * powx)) % _basefield
            x_den = (x_den + (_Xden[i] * powx)) % _basefield
         powx = powx * x
      return  [(x_num * gmp.invert(x_den,_basefield)) % _basefield ,(y*(y_num * gmp.invert(y_den,_basefield))) % _basefield]

   def _GLV2PointMulG1(a,P):
      _2P  = _doubleAffine(P.x, P.y)
      _2phiP = [(_2P[0] * _Wx) % _basefield, _2P[1]]
      T = [[(P.x * -(_Wx+1)) % _basefield, (-P.y) % _basefield]]
      T = T + [_addAffine(_2P[0], _2P[1], T[0][0], T[0][1])]
      T = T + [_addAffine(_2P[0], _2P[1], T[1][0], T[1][1])]
      T = T + [_addAffine(_2P[0], _2P[1], T[2][0], T[2][1])]    
      for i in range((_tableSize >> 1) - _blockSize):
         T = T + [_addAffine(_2phiP[0], _2phiP[1], T[-_blockSize][0],T[-_blockSize][1])]
      _scalar = a % _r
      _alpha = (_Lamda | _scalar) & 1
      a = (_r - _scalar) * (1 - _alpha) + _scalar * _alpha   
      _code = Recs._recordScalarGLV2(a,_Lamda)
      _fi   = _code & 1
      _sig  = (_code & 2) - 1 
      _idx  = (_code & Recs._wDMask) >> 2
      _aP   = [(_Wx * _fi + (1 - _fi)) * T[_idx][0], _sig * (1 - 2 * _fi) * T[_idx][1]]+ [1]     
      _code = _code >> Recs._wDSize
      while (_code != 1):
               _fi    = _code & 1   
               _sig  = (_code & 2) - 1
               _idx  = (_code & Recs._wDMask) >> 2
               _code =  _code >> Recs._wDSize
               _aP = _doubleProjective(_aP[0], _aP[1], _aP[2])
               _aP = _doubleProjective(_aP[0], _aP[1], _aP[2])
               _aP = _doubleProjective(_aP[0], _aP[1], _aP[2])
               _aP = _addMixed(_aP[0], _aP [1], _aP[2],(_Wx * _fi + (1 - _fi)) * T[_idx][0], _sig * (1 - 2 * _fi) * T[_idx][1])   
      _ = gmp.invert(_aP[2], _basefield)
      return ECFP(_aP[0] * _, ((_alpha << 1) - 1) * _aP[1] * _)

   class ECFP :
      def __init__(self,x,y=None,dotest=False):
         self.istorsion = False
         if x is None:
            self.infinity = True
            self.x, self.y, self.z = 0, 1, 0
         else:
            if y is None:
              self.x = x % _basefield if type(x)==gmp.mpz else gmp.mpz(x) % _basefield
              _ = Ar.rsqrt((x**3+ECFP.B) % _basefield,_basefield)
              if (_ != None) : self.infinity, self.y, self.z = False, _, gmp.mpz(1)
              else :raise TypeError("Invalide curve point parametres ...")
            else:
              self.x = x % _basefield if type(x)==gmp.mpz else gmp.mpz(x) % _basefield
              self.y = y % _basefield if type(y)==gmp.mpz else gmp.mpz(y) % _basefield
              self.z = gmp.mpz(1)
              self.infinity = False
              if (dotest) and (y**2 % _basefield != (x**3+ECFP.B) % _basefield) : raise TypeError("Invalide curve point parametres ...")
      
      def __str__(self):return "("+str(self.x)+" , "+str(self.y)+")" if not self.infinity else "Infinity"
      __repr__ = __str__
      def __add__(self,q):
        if self.infinity:
           if q.infinity : return ECFP(None)
           else : return ECFP(q.x,q.y)
        else:
           if q.infinity : return self.copy()
           else:
            if self.x == q.x:
               if self.y == q.y:return ECFP((res := _doubleAffine(self.x, self.y))[0], res[1])
               else : return ECFP(None)
            else : return ECFP((res := _addAffine(self.x,self.y,q.x,q.y))[0], res[1])

      def __neg__(self)  : return ECFP(self.x,-self.y)
      def __sub__(self,q): return self + (-q)
      def __eq__(self,q) : return (self.x == q.x) & (self.y == q.y) if not(self.infinity | q.infinity) else (self.infinity == q.infinity)
      def __ne__(self,q) : return (self.infinity != q.infinity) | (self.x != q.x) | (self.y != q.y)
      def __rmul__(self,b):
         # Constant-time multiplication using w-sliding window (w=3)
         # Faster than Montgomery Ladder, use affine coordinates 
         if (type(b) != int) & (type(b) != gmp.mpz) : 
            raise TypeError("Invalide scalar value for multiplication ...")
         else :
            b = abs(b) % _r
            if (self.istorsion) and (b.bit_length()>(_r.bit_length()>>4)): return _GLV2PointMulG1(b,self)
            else:
               _outSig = abs(b+1) - abs(b)               
               if self.infinity: return ECFP(None)
               if b==0 : return ECFP(None)
               if b==2 : return ECFP((res:=_doubleAffine(self.x,self.y))[0], _outSig * res[1])
               else:
                  T = [_doubleAffine(self.x, self.y)] + [[self.x, self.y]]
                  T = T + [_addAffine(T[0][0], T[0][1], self.x, self.y)]
                  T = T + [_addAffine(T[0][0], T[0][1], T[2][0], T[2][1])]
                  T = T + [_addAffine(T[0][0], T[0][1], T[3][0], T[3][1])]
                  _code = Recs._recordOneScalar(b+(b & 1)+1)               
                  _aP   = T[(_code & (Recs._wMask >> 1)) + 1]+[1]                
                  _code = _code >> (Recs._wSize-1)
                  while (_code != 1):
                        _sig = 2 * (_code & 1)-1
                        _idx = ((_code & Recs._wMask) >> 1) + 1
                        _aP  = _doubleProjective(_aP[0], _aP[1], _aP[2])
                        _aP  = _doubleProjective(_aP[0], _aP[1], _aP[2])
                        _aP  = _doubleProjective(_aP[0], _aP[1], _aP[2])
                        _aP  = _addMixed(_aP[0], _aP[1], _aP[2], T[_idx][0], _sig * T[_idx][1])
                        _code =  _code >> Recs._wSize
                  _aP  = _addMixed(_aP[0], _aP[1], _aP[2], T[1 - (b & 1)][0], -T[1 - (b & 1)][1])
                  if _aP[2] == 0 : return ECFP(None) 
                  else:                   
                     _ = gmp.invert(_aP[2], _basefield)
                     return ECFP(_aP[0] * _, _outSig  * _ * _aP[1])      
      def phi(self) : 
         return ECFP(self.x*_Wx % _basefield, self.y)
      def copy(p) : 
         return ECFP(p.x,p.y)
      def pickRandomPoint():
         _ = _swumapping(gmp.mpz(random.randint(0, _basefield-1)))
         return ECFP(_[0], _[1])
      def pickTorsionPoint() : 
         _ = _h * ECFP.pickRandomPoint() # Cofactor cleaning
         _.istorsion = True 
         return _
      def pickRandomScalar() : 
         return gmp.mpz(random.randint(0, (ECFP.r ^ (1 << (ECFP.r.bit_length() - 1)))) | (1 << (ECFP.r.bit_length() - 1)) )
      def hashtoG1(identifier, mode = 0):
         #     mode=0: Encode to Curve (NU-encode-to-curve), mode=1: Random Oracle model (RO-hash-to-curve)
         #     https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-06#name-roadmap
         if mode == 0 :
            _ = _swumapping(gmp.mpz(HashToField(identifier, _basefield, extdegree = 1, count = 1)[0][0]))
            return _h * ECFP(_[0], _[1])
         else :
            _  = HashToField(identifier, _basefield, extdegree = 1, count = 2)
            _1 = _swumapping(gmp.mpz(_[0][0]))
            _2 = _swumapping(gmp.mpz(_[1][0]))
            _1, _2 = _addAffine(_1[0], _1[1], _2[0], _2[1])
            _ = _h * ECFP(_1,_2)
            _.istorsion = True
            return _
      def isOnCurve(self) : 
         return (self.y**2 % _basefield == (self.x**3 + ECFP.B) % _basefield)
      def isTorsion(self):
         #     Check if a point P is a Torsion Point
         #     According to https://eprint.iacr.org/2022/352.pdf we have to check that  ψ(P)+lamda*P="Infinity"
         self.istorsion = False
         self.istorsion = _Lamda * self == self.phi()
         return self.istorsion
      def toBytes(p):
         #     Point compression/Serialization as described by ZCach serialization format
         #     https://www.ietf.org/archive/id/draft-irtf-cfrg-pairing-friendly-curves-11.html#name-zcash-serialization-format-
         C_bit, I_bit, S_bit = 1, int(p.infinity), 0 if p.infinity else ((1+Fpsgn0(p.y, _basefield)) >>1)
         m_byte   = (C_bit << 7) | (I_bit << 6) | (((S_bit + 1) >> 1) << 5)
         x_string = I2OSP(0, _sizeInBytes) if p.infinity else I2OSP(p.x, _sizeInBytes)
         if _basefield.bit_length() % 8 <= 5:return bytes([x_string[0] | m_byte]) + x_string[1:]
         else: return bytes([m_byte]) + x_string 
      
      def fromBytes(bytearray):
         #     Point de-compression/de-Serialization as described by ZCach serialization format
         #     https://www.ietf.org/archive/id/draft-irtf-cfrg-pairing-friendly-curves-11.html#name-zcash-serialization-format-
         m_byte= bytearray[0] & 0xE0
         if _basefield.bit_length() % 8<=5 : bytearray = bytes([bytearray[0] & 0x1F]) + bytearray[1:]
         else: bytearray = bytearray[1:]
         if (m_byte == 0xE0) : raise TypeError("Invalide compressed point format ...") 
         if m_byte & 0x80 != 0 :
            if len(bytearray) != _sizeInBytes : raise TypeError("Invalide compressed point format ...")
         else :
            if len(bytearray) != (_sizeInBytes << 1) : raise TypeError("Invalide compressed point format ...")
         if (m_byte & 0x40 != 0) :
            if (any([e != 0 for e in bytearray])) : raise TypeError("Invalide compression of an infinity point ...")
            else : return ECFP(None)
         else :
            if len(bytearray) == (_sizeInBytes << 1) :
               x = gmp.mpz(OS2IP(bytearray[:48]))
               y = gmp.mpz(OS2IP(bytearray[48:]))
               return ECFP(x, y, dotest = True)
            else :
               x = gmp.mpz(OS2IP(bytearray))
               y = Ar.rsqrt((x**3 + ECFP.B) % _basefield, _basefield)
               if y is None : raise TypeError("Invalide point: not in the curve ...")
               else :
                  if ((Fpsgn0(y,_basefield) + 1)>>1) == int(m_byte & 0x20 != 0) : return ECFP(x, y)
                  else : return ECFP(x, -y)
      def toBase64(self):
         return base64.b64encode(self.toBytes()).decode("ascii")
      def fromBase64(str):
         return ECFP.fromBytes(base64.b64decode(str))

   _basefield = CurveParams["p"]
   _sizeInBytes = (_basefield.bit_length() // 8)+int(_basefield.bit_length() % 8 != 0)
   _r = CurveParams["r"]
   _u = CurveParams["u"]
   _h = CurveParams["h1bis"]     #  reduced Cofactor (1-u), "Wahby and Boneh" https://eprint.iacr.org/2019/403  , section 5   
   #   Parametres of the Endomorphisme for GLV multiplication
   _Lamda = CurveParams["lamda"]
   _Wx = CurveParams["w"]   
   # Windows signed representation parameter
   _tableSize = (1 << (Recs._wDSize - 1))
   _blockSize = (1 << (Recs._wSize - 1))
   #    Parametres of the constant-time Hash to G1 (swu + Isogeny)
   _swuZ  = CurveParams["swuParamsG1"]["Z"]
   _swuA  = CurveParams["swuParamsG1"]["swuA"]
   _swuB  = CurveParams["swuParamsG1"]["swuB"]
   _BdivA = (-(_swuB* gmp.invert(_swuA,_basefield))) % _basefield
   _invZ  = (-(gmp.invert(_swuZ,_basefield))) % _basefield
   _Xnum  = CurveParams["swuParamsG1"]["Xnum"]
   _Xden  = CurveParams["swuParamsG1"]["Xden"]
   _Ynum  = CurveParams["swuParamsG1"]["Ynum"]
   _Yden  = CurveParams["swuParamsG1"]["Yden"]
   ECFP.u = _u
   ECFP.r = _r
   ECFP.h = _h
   ECFP.B = CurveParams["B"]
   ECFP.Description = CurveParams["Description"]
   return ECFP

#--------------------------------------------------------------------------------------------------------------------------------------------------------------------#
# Elliptic Curves implementation Over Fp2:
#                  - Affine coordinates implementation (field inversion is sufficently fast on gmp) 
#                  - SWU points mapping using isogenies
#                  - GLS Multuplication for Torsion points in G2
#                  - Sliding window multiplication for points not in G2 (in E(Fp2))
#                  - Constant-time implementation
#--------------------------------------------------------------------------------------------------------------------------------------------------------------------#
def ECFP2(CurveParams):  
   _add    =  lambda x1,y1,x2,y2:[(_1:=((_0:=((y2-y1)/(x2-x1)))**2-x2-x1)),(_0*(x2-_1)-y2)]
   _double =  lambda x,y:[(_1:=((_0:=((3*x**2)/(2*y)))**2-2*x)),(_0*(x-_1)-y)] 
  
   def _swumapping(u):    
         #     Simplified Shallue-van de Woestijne-Ulas Method (Simplified SWU for AB == 0)
         #     https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-05#section-6.6.3
         #     https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-05#appendix-C.3
         t1 = _swuZ * u**2
         t2 = t1**2
         x1 = (t1 + t2).inverse()
         if x1 == 0: x1 = _invZ
         else : x1 = x1 + 1
         x1 = x1 * _BdivA 
         gx1 = (x1**2 + _swuA) * x1 + _swuB      
         if gx1.isqr():
            y = gx1.sqrt()
            if FpMsgn0(u,_basefield) != FpMsgn0(y,_basefield):y = -y
            x = x1
         else: 
            x2 = t1 * x1 
            t2 = t1 * t2
            gx2 = gx1 * t2 
            y = gx2.sqrt()
            if FpMsgn0(u,_basefield) != FpMsgn0(y,_basefield):y = -y
            x = x2
         # isogeny map from E' to E "Wahby and Boneh" https://eprint.iacr.org/2019/403  
         x2 = x.sqr()
         x3 = x2 * x
         x_num = _Xnum[3] * x3 + _Xnum[2] * x2 + _Xnum[1] * x + _Xnum[0]
         x_den = _Xden[2] * x2 + _Xden[1] * x + _Xden[0]
         y_num = _Ynum[3] * x3 + _Ynum[2] * x2 + _Ynum[1] * x + _Ynum[0]
         y_den = _Yden[3] * x3 + _Yden[2] * x2 + _Yden[1] * x + _Yden[0]
         return  [x_num / x_den,y * (y_num / y_den)]

   def _GLSPointMulG2(a,P):
         #     GLS Implementation of points multiplication on G2 for the BLS12 Curve
         #     Faster multiplication for Torsion Points from G2
         #     Joppe W. Bos, Craig Costello, and Michael Naehrig https://eprint.iacr.org/2013/458.pdf
         #     Constant-Time multiplication for elements in G2
         #     Point's operations are performent using affine coordinates          
         code= Recs._recordScalarGLS4(a ,abs(_u),ECFP2.r)
         P1 = P.phi()
         P2 = P1.phi()
         P3 = P2.phi()
         sig_u = abs(_u+1) - abs(_u)
         T = [[P.x,P.y]]
         T = T + [_add(P1.x,sig_u * P1.y,T[0][0],T[0][1])]
         T = T + [_add(P2.x,P2.y,T[0][0],T[0][1])] 
         T = T + [_add(P2.x,P2.y,T[1][0],T[1][1])]
         T = T + [_add(P3.x,sig_u * P3.y,T[0][0],T[0][1])]
         T = T + [_add(P3.x,sig_u * P3.y,T[1][0],T[1][1])]
         T = T + [_add(P3.x,sig_u * P3.y,T[2][0],T[2][1])]
         T = T + [_add(P3.x,sig_u * P3.y,T[3][0],T[3][1])]
         out_sig = (1 - ((code & 1) << 1))
         code = code >> 1
         sign = ((code & 1) << 1) - 1
         idx  = (code & 15) >> 1
         res  = [T[idx][0],sign * T[idx][1]]
         code = code >> 4
         while code != 1:        
            res=_double(res[0],res[1])
            sign = ((code & 1) << 1) - 1
            idx  = (code & 15) >> 1     
            res  = _add(res[0],res[1],T[idx][0],sign * T[idx][1])
            code = code >> 4
         return ECFP2(res[0],out_sig * res[1])       
   def _cleancofactor(P):
      # Fast way to clean Cofactor of G2 using Endomorphisme 
      # using "Budroni-Pintore" approach (https://ia.cr/2017/419).
      xP = _u * P
      phiP = P.phi()
      _ = 2 * (phiP.phi()) + _u * (xP + phiP) - xP - phiP - P 
      _.istorsion = True
      return _
  
   class ECFP2 :
         def __init__(self,x,y=None,dotest=False):         
            self.istorsion = False
            if x is None:
               self.infinity = True
            else:
               if y is None:              
                  self.x = x 
                  _ = (x**3 + ECFP2.B).sqrt()
                  if not(_ is None):self.infinity,self.y,self.z = False,_,ECFP2.field([1,0])
                  else :raise TypeError("Invalide curve point parametres ...")  
               else:
                  self.x = x if type(x) == ECFP2.field else ECFP2.field(x) 
                  self.y = y if type(x) == ECFP2.field else ECFP2.field(y) 
                  self.z = ECFP2.field([1,0])
                  self.infinity = False
                  if (dotest) and (not(y.sqr() ==(x**3 + ECFP2.B))):raise TypeError("Invalide curve point parametres ...")  
         def __str__(self):
            return "("+str(self.x) + " , "+str(self.y)+")" if not self.infinity else "Infinity"
         __repr__ = __str__     
         def __add__(self,q):
            if self.infinity:
               if q.infinity:return ECFP2(None)
               else : return q.copy()
            else:
               if q.infinity:return self.copy()
               else:
                  if self.x == q.x:
                     if self.y == q.y:
                        _res = _double(self.x, self.y)
                        return ECFP2(_res[0],_res[1]) 
                     else: return ECFP2(None)               
                  else:
                     _res = _add(self.x, self.y, q.x, q.y)
                     return ECFP2(_res[0],_res[1]) 
         def __neg__(self):  
             return ECFP2(self.x, -self.y)
         def __sub__(self,q):
             return self +(-q)
         def __eq__(self,q): 
             return (self.x== q.x) and (self.y == q.y) if not(self.infinity | q.infinity) else (self.infinity == q.infinity)
         def __ne__(self,q): 
             return (self.infinity != q.infinity) or (self.x != q.x) or (self.y != q.y)
         def __rmul__(self,b):
            # Constant-time multiplication using w-sliding window (w=3)
            # Faster than Montgomery Ladder, use affine coordinates                           
            if (type(b) != int) & (type(b) != gmp.mpz) : 
                  raise TypeError("Invalide scalar value for multiplication ...")
            else :
               _outSig = abs(b+1) - abs(b)
               b = abs(b) % ECFP2.r
               if (self.istorsion) and (b.bit_length()>(ECFP2.r.bit_length()>>4)): return _GLSPointMulG2(b,self)
               else :                                    
                  if self.infinity: return ECFP2(None)
                  if b==0 :return ECFP2(None)
                  if b==2 :return ECFP2((res:=_double(self.x,self.y))[0], _outSig * res[1])
                  else:
                     T = [_double(self.x, self.y)] + [[self.x, self.y]]
                     T = T + [_add(T[0][0], T[0][1], self.x, self.y)]
                     T = T + [_add(T[0][0], T[0][1], T[2][0], T[2][1])]
                     T = T + [_add(T[0][0], T[0][1], T[3][0], T[3][1])]
                     _code = Recs._recordOneScalar(b + (b & 1) + 1)               
                     _aP   = T[(_code & (Recs._wMask >> 1)) + 1]+[1]                
                     _code = _code >> (Recs._wSize-1)
                     while (_code != 1):
                              _sig = 2 * (_code & 1)-1
                              _idx = ((_code & Recs._wMask) >> 1) + 1
                              _aP  = _double(_aP[0], _aP[1])
                              _aP  = _double(_aP[0], _aP[1])
                              _aP  = _double(_aP[0], _aP[1])
                              _aP  = _add(_aP[0], _aP[1], T[_idx][0], _sig * T[_idx][1])
                              _code =  _code >> Recs._wSize
                     _aP  = _add(_aP[0], _aP[1], T[1 - (b & 1)][0], -T[1 - (b & 1)][1])
                     return ECFP2(_aP[0] , _outSig * _aP[1])  
         def phi(self):
            # Endomorphisme Phi(P)=u*P: Twist->Frobinus->Un-twist (in M-Type Mode for BLS12-381)
            # Twist : (x,y)->(x/w^2,y/w^3)=(x/(1+u)^(1/3), y/(1+u)^(1/2))
            # Frobinus :(x,y)->(x^P,y^P)
            # Un-Twist : (x,y)->(x*w^2,y*w^3)=(x*(1+u)^(1/3), y*(1+u)^(1/2))
            # Combinaison of the three maps is equivalent to one multiplication by constants: (c1,c2)=(1/((1+u)^((prime-1) div 3)),1/((1+u)^((prime-1) div 2)))             
            return ECFP2(_phic1 * self.x.conjugate(),_phic2 * self.y.conjugate())
         def copy(self):
            return ECFP2(self.x,self.y) 
         def pickrandom():
            _=_swumapping(ECFP2.field.pickrandom())  
            return ECFP2(_[0],_[1])
         def pickRandomScalar(): 
            # return gmp.mpz(random.randint(0, (ECFP2.r ^ (1 << (ECFP2.r.bit_length() - 1)))) | (1 << (ECFP2.r.bit_length() - 1)) )
            return gmp.mpz(random.randint(1 << (ECFP2.r.bit_length() - 4), 1 << (ECFP2.r.bit_length() - 2)))
         def pickTorsionPoint(): 
            return _cleancofactor(ECFP2.pickrandom()) # Cofactor cleaning of a random point 
         def hashtoG2(identifier,mode=0):
            #     mode=0: Encode to Curve (NU-encode-to-curve), mode=1: Random Oracle model (RO-hash-to-curve)
            #     https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-06#name-roadmap 
            if mode == 0:
                  _hf = HashToField(identifier,_basefield,extdegree=2,count=1)
                  _ = _swumapping(ECFP2.field([gmp.mpz(_hf[0][0]),gmp.mpz(_hf[0][1])]))         
                  return _cleancofactor(ECFP2(_[0],_[1]))
            else:
                  _hf = HashToField(identifier,_basefield,extdegree=2,count=2)
                  _1 = _swumapping(ECFP2.field([gmp.mpz(_hf[0][0]),gmp.mpz(_hf[0][1])]))         
                  _2 = _swumapping(ECFP2.field([gmp.mpz(_hf[1][0]),gmp.mpz(_hf[1][1])]))         
                  _1,_2 = _add(_1[0],_1[1],_2[0],_2[1])
                  return _cleancofactor(ECFP2(_1,_2))                    
         def isOnCurve(self):
            return self.y**2 == (self.x**3) + ECFP2.B
         def isTorsion(self):
            # Check if a point P is a Torsion Point
            # According to https://eprint.iacr.org/2019/814.pdf we have to check that  u*ψ3(P)-ψ2(P)+P="Infinity"
            # Or with according to https://hackmd.io/@yelhousni/bls12_subgroup_check that :−z⋅ψ(ϕ(Q))+ϕ(Q)+Q="Infinity" when  ϕ(P) is the endomorphisme of G1 (w*x,y)
            # However, all theses are equivalents to check that u*P=ψ(P) (we can show that ψ4(P)-ψ(P)+P="Infinity" for every point on the curve)
            # Same hint pointed by Scott :https://eprint.iacr.org/2021/1130.pdf        
            self.istorsion = False
            self.istorsion = (_u*self == self.phi())
            return self.istorsion
         def toBytes(self):          
            #     Point compression/Serialization as described by ZCach serialization format
            #     https://www.ietf.org/archive/id/draft-irtf-cfrg-pairing-friendly-curves-11.html#name-zcash-serialization-format-
            C_bit,I_bit,S_bit = 1,int(self.infinity),0 if self.infinity else ((1 + FpMsgn0(self.y,_basefield)) >> 1)
            m_byte = C_bit << 7 | I_bit << 6 | S_bit << 5
            x_string = I2OSP(0,_sizeInBytes << 1) if self.infinity else I2OSP(self.x._raw[0],_sizeInBytes) + I2OSP(self.x._raw[1],_sizeInBytes)
            if _basefield.bit_length() % 8 <= 5:return bytes([x_string[0] | m_byte]) + x_string[1:]
            else: return bytes([m_byte]) + x_string    
         def fromBytes(bytearray):
            #     Point de-compression/de-Serialization as described by ZCach serialization format
            #     https://www.ietf.org/archive/id/draft-irtf-cfrg-pairing-friendly-curves-11.html#name-zcash-serialization-format-
            m_byte = bytearray[0] & 0xE0
            if _basefield.bit_length() % 8 <= 5 : bytearray = bytes([bytearray[0] & 0x1F]) + bytearray[1:]
            if (m_byte == 0xE0):raise TypeError("Invalide compressed point format ...")  
            if m_byte & 0x80 != 0:
               if len(bytearray) != _sizeInBytes << 1:raise TypeError("Invalide compressed point format ...")  
            else:
               if len(bytearray) != _sizeInBytes << 2:raise TypeError("Invalide compressed point format ...")  
            if (m_byte & 0x40!=0):
               if (any([e != 0 for e in bytearray])): raise TypeError("Invalide compression of an infinity point ...")  
               else :return ECFP2(None)
            else:
               if len(bytearray) == _sizeInBytes << 2:
                  x = ECFP2.field([OS2IP(bytearray[:_sizeInBytes]),OS2IP(bytearray[_sizeInBytes:_sizeInBytes << 1])])
                  y = ECFP2.field([OS2IP(bytearray[_sizeInBytes << 1:_sizeInBytes << 2]),OS2IP(bytearray[_sizeInBytes << 2:])])
                  return ECFP2(x,y,dotest = True)
               else:
                  x = ECFP2.field([OS2IP(bytearray[:_sizeInBytes]),OS2IP(bytearray[_sizeInBytes:])])
                  y = (x**3 + ECFP2.B).sqrt()
                  if y is None:raise TypeError("Invalide point: not in the curve ...")  
                  else:
                     if ((FpMsgn0(y,_basefield) + 1) >> 1) == int(m_byte & 0x20!=0):return ECFP2(x,y)
                     else :return ECFP2(x,-y)
         def toBase64(self):
            return base64.b64encode(self.toBytes()).decode("ascii")
         def fromBase64(str):
            return ECFP2.fromBytes(base64.b64decode(str))

   _basefield = CurveParams["p"]
   _sizeInBytes = (_basefield.bit_length() // 8)+int(_basefield.bit_length() % 8 != 0)
   ECFP2.field = Extf.F2(CurveParams)  
   ECFP2.B = ECFP2.field(CurveParams["Btw"])  
   ECFP2.r = CurveParams["r"]
   ECFP2.h = CurveParams["h2"]
   ECFP2.u = CurveParams["u"]
   ECFP2.w = CurveParams["w"]
   _u = CurveParams["u"]
   _phic1 = ECFP2.field(CurveParams["phiConsts"][0])
   _phic2 = ECFP2.field(CurveParams["phiConsts"][1])
   #      Parametres of the constant-time Hash to G2 (swu+Isogeny)
   _swuZ = ECFP2.field(CurveParams["swuParamsG2"]["Z"])
   _swuA = ECFP2.field(CurveParams["swuParamsG2"]["swuA"])
   _swuB = ECFP2.field(CurveParams["swuParamsG2"]["swuB"])
   _BdivA = -_swuB/_swuA
   _invZ = -1/_swuZ  
   _Xnum = [ECFP2.field(i) for i in CurveParams["swuParamsG2"]["Xnum"]]
   _Ynum = [ECFP2.field(i) for i in CurveParams["swuParamsG2"]["Ynum"]]
   _Yden = [ECFP2.field(i) for i in CurveParams["swuParamsG2"]["Yden"]]
   _Xden = [ECFP2.field(i) for i in CurveParams["swuParamsG2"]["Xden"]]
   return ECFP2


#--------------------------------------------------------------------------------------------------------------------------------------------------------------------#
# Elliptic Curves implementation Over Fp4:
#                  - Affine coordinates implementation (field inversion is sufficently fast on gmp) 
#                  - SWU points mapping using isogenies
#                  - GLS Multuplication for Torsion points in G2
#                  - Sliding window multiplication for points not in G2 (in E(Fp4))
#                  - Constant-time implementation
#--------------------------------------------------------------------------------------------------------------------------------------------------------------------#
def ECFP4(CurveParams):
   _add    =  lambda x1,y1,x2,y2:[(_1:=((_0:=((y2-y1)/(x2-x1)))**2-x2-x1)),(_0*(x2-_1)-y2)]
   _double =  lambda x,y:[(_1:=((_0:=((3*x**2)/(2*y)))**2-2*x)),(_0*(x-_1)-y)] 
    
   def _swumapping(u):
      #     Simplified Shallue-van de Woestijne-Ulas Method (Simplified SWU for AB == 0)
      #     https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-05#section-6.6.3
      #     https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-05#appendix-C.3
      t1 = _swuZ * u**2
      t2 = t1**2
      x1 = (t1 + t2).inverse()
      if x1 == 0: x1 = _invZ
      else : x1 = x1+1
      x1 = x1 * _BdivA
      gx1 = (x1**2 + _swuA) * x1 + _swuB
      if gx1.isqr():
         y = gx1.sqrt()
         if FpMsgn0(u,_basefield) != FpMsgn0(y,_basefield):y = -y
         x = x1
      else:
         x2 = t1 * x1
         t2 = t1 * t2
         gx2 = gx1 * t2
         y = gx2.sqrt()
         if FpMsgn0(u,_basefield) != FpMsgn0(y,_basefield):y = -y
         x = x2
      # isogeny map from E' to E "Wahby and Boneh" https://eprint.iacr.org/2019/403
      x_num,x_den,y_num,y_den = _Xnum[0],_Xden[0],_Ynum[0],_Yden[0]
      powx = x
      for i in range(1,len(_Ynum)):
         y_num = (y_num + _Ynum[i] * powx)
         y_den = (y_den + _Yden[i] * powx)
         if i < len(_Xnum):
            x_num = (x_num + _Xnum[i] * powx)
            x_den = (x_den + _Xden[i] * powx)
         powx = powx * x
      return  [x_num / x_den,y * (y_num / y_den)]
   def _invphi(P):
      return ECFP4(ECFP4.field([(P.x._raw[1] - P.x._raw[0]) * _frobConsts[6],(P.x._raw[1] + P.x._raw[0]) * _frobConsts[6],-P.x._raw[2] * _frobConsts[5],\
                                P.x._raw[3] * _frobConsts[5]]), \
             ECFP4.field([(P.y._raw[3]) * _frobConsts[1] ,(P.y._raw[2]) * _frobConsts[1] ,-(P.y._raw[0]) * (_frobConsts[2]) ,(P.y._raw[1]) * (_frobConsts[2])]))
   def _phi(x):
      return [ECFP4.field([(x[0]._raw[0] - x[0]._raw[1]) * _frobConsts[7],-(x[0]._raw[0] + x[0]._raw[1]) * _frobConsts[7],x[0]._raw[2] * (_frobConsts[5]+1),\
                           -x[0]._raw[3] * (_frobConsts[5] + 1) ]),            \
             ECFP4.field([-(x[1]._raw[2]) * _frobConsts[1] ,(x[1]._raw[3]) * _frobConsts[1] ,(x[1]._raw[1]) * (_frobConsts[2]) ,(x[1]._raw[0]) * (_frobConsts[2])])]
   def _phi4(x):
      return [ECFP4.field([-x[0]._raw[0] * (_frobConsts[5] + 1) ,-x[0]._raw[1] * (_frobConsts[5] + 1),-x[0]._raw[2] * (_frobConsts[5] + 1) ,\
              -x[0]._raw[3]*(_frobConsts[5]+1)]), ECFP4.field([-x[1]._raw[0],-x[1]._raw[1],-x[1]._raw[2],-x[1]._raw[3]])]
   def _GLSPointMulG2(a,P):
      #     GLS Implementation of points multiplication on G2 for the BLS24 Curve (8-GLS)
      #     Joppe W. Bos, Craig Costello, and Michael Naehrig https://eprint.iacr.org/2013/458.pdf
      #     Constant-Time multiplication for elements in G2
      #     Point's operations are performent using affine coordinates
      code = Recs._recordScalarGLS8(a,abs(_u),ECFP4.r) 
      P1 = _phi([P.x,P.y])
      P2 = _phi(P1)
      P3 = _phi(P2)
      sig_u = abs(_u+1) - abs(_u)
      T1 = [[P.x,P.y]]
      T1 = T1 + [_add(P1[0],sig_u * P1[1],T1[0][0],T1[0][1])]
      T1 = T1 + [_add(P2[0],P2[1],T1[0][0],T1[0][1])] 
      T1 = T1 + [_add(P2[0],P2[1],T1[1][0],T1[1][1])]
      T1 = T1 + [_add(P3[0],sig_u * P3[1],T1[0][0],T1[0][1])]
      T1 = T1 + [_add(P3[0],sig_u * P3[1],T1[1][0],T1[1][1])]
      T1 = T1 + [_add(P3[0],sig_u * P3[1],T1[2][0],T1[2][1])]
      T1 = T1 + [_add(P3[0],sig_u * P3[1],T1[3][0],T1[3][1])]
      T2 = [_phi4(i) for i in T1]
      out_sig = (1 - ((code & 1) << 1))
      code = code >> 1
      c1, c2 = code & 15, (code >> 4) & 15
      s1, s2 = ((c1 & 1) << 1) - 1 , ((c2 & 1) << 1) - 1
      res = _add(T1[c1 >> 1][0], s1 * T1[c1 >> 1][1], T2[c2 >> 1][0], s2 * T2[c2 >> 1][1])
      code = code >> 8
      while (code != 1):
         res = _double(res[0], res[1]) 
         c1, c2 = code & 15, (code >> 4) & 15
         s1, s2 = ((c1 & 1) << 1) - 1 , ((c2 & 1) << 1) - 1
         res = _add(res[0], res[1], T1[c1 >> 1][0], s1 * T1[c1 >> 1][1])
         res = _add(res[0], res[1], T2[c2 >> 1][0], s2 * T2[c2 >> 1][1])
         code = code >> 8
      return ECFP4(res[0],out_sig * res[1])
   def _cleancofactor(P):
      # Fast way to clean Cofactor of G2 using Endomorphisme
      # using "Budroni-Pintore" approach (https://ia.cr/2017/419) (personal use of inverted frobenius for optimization). 
      _ = _phi4([P.x,P.y])
      P4 = ECFP4(_[0],_[1])
      xP = (_u-1)*_invphi(P4)
      _ = 2 * P4 - P + xP
      for i in range(3):
         xP = _u * _invphi(xP)
         _ = _ + xP
      return _
  
   class ECFP4 :
      def __init__(self,x,y = None,dotest = False):
         self.istorsion = False
         if x is None:
            self.infinity = True
         else:
            if y is None:
              self.x = x if type(x) == ECFP4.field else ECFP4.field(x)
              _ = (x**3 + ECFP4.B).sqrt()
              if not(_ is None):self.infinity,self.y,self.z = False,_,ECFP4.field([1,0,0,0])
              else :raise TypeError("Invalide curve point parametres ...")
            else:
              self.x = x if type(x) == ECFP4.field else ECFP4.field(x)
              self.y = y if type(x) == ECFP4.field else ECFP4.field(y)
              self.z = ECFP4.field([1,0,0,0])
              self.infinity = False
              if (dotest) and (not(y.sqr() == (x**3 + ECFP4.B))):raise TypeError("Invalide curve point parametres ...")
      def __str__(self):return "("+str(self.x) + " , "+str(self.y)+")" if not self.infinity else "Infinity"
      __repr__ = __str__
      def __add__(self,q):
        if self.infinity:
           if q.infinity:return ECFP4(None)
           else : return q.copy()
        else:
           if q.infinity:return self.copy()
           else:
            if self.x == q.x:
               if self.y == q.y:
                  _res = _double(self.x,self.y)
                  return ECFP4(_res[0],_res[1])
               else: return ECFP4(None)
            else:
               _res = _add(self.x,self.y,q.x,q.y)
               return ECFP4(_res[0],_res[1])
      def __neg__(self):return ECFP4(self.x,-self.y)
      def __sub__(self,q):return self + (-q)
      def __eq__(self,q): return (self.x == q.x) and (self.y==q.y) if not(self.infinity | q.infinity) else (self.infinity == q.infinity)
      def __ne__(self,q): return (self.infinity != q.infinity) or (self.x != q.x) or (self.y !=q.y)
      def __rmul__(self,b):
            # Constant-time multiplication using w-sliding window (w=3)
            # Faster than Montgomery Ladder, use affine coordinates                           
            if (type(b) != int) & (type(b) != gmp.mpz) : 
                  raise TypeError("Invalide scalar value for multiplication ...")
            else :
               _outSig = abs(b+1) - abs(b)
               b = abs(b) % ECFP4.r
               if (self.istorsion) and (b.bit_length() > (ECFP4.r.bit_length() >> 4)): return _GLSPointMulG2(b,self)
               else :
                  if self.infinity: return ECFP4(None)
                  if b == 0 :return ECFP4(None)
                  if b == 2 :return ECFP4((res := _double(self.x,self.y))[0], _outSig * res[1])
                  else:
                     T = [_double(self.x, self.y)] + [[self.x, self.y]]
                     T = T + [_add(T[0][0], T[0][1], self.x, self.y)]
                     T = T + [_add(T[0][0], T[0][1], T[2][0], T[2][1])]
                     T = T + [_add(T[0][0], T[0][1], T[3][0], T[3][1])]
                     _code = Recs._recordOneScalar(b + (b & 1) + 1)               
                     _aP   = T[(_code & (Recs._wMask >> 1)) + 1]+[1]                
                     _code = _code >> (Recs._wSize-1)
                     while (_code != 1):
                              _sig = 2 * (_code & 1)-1
                              _idx = ((_code & Recs._wMask) >> 1) + 1
                              _aP  = _double(_aP[0], _aP[1])
                              _aP  = _double(_aP[0], _aP[1])
                              _aP  = _double(_aP[0], _aP[1])
                              _aP  = _add(_aP[0], _aP[1], T[_idx][0], _sig * T[_idx][1])
                              _code =  _code >> Recs._wSize
                     _aP  = _add(_aP[0], _aP[1], T[1 - (b & 1)][0], -T[1 - (b & 1)][1])
                     return ECFP4(_aP[0] , _outSig * _aP[1])  
      def phi(self):
          # Endomorphisme Phi(P)=u*P: Twist->Frobinus->Un-twist (in D-Type Mode for BLS24)
          # Twist : (x,y)->(x*z^2,y*z^3)
          # Frobinus :(x,y)->(x^P,y^P)
          # Un-Twist : (x,y)->(x/z^2,y/z^3)
          # Combinaison of the three maps is equivalent to one multiplication by constants: (c1,c2)=(z^(2*(prime-1))),1/(z^(3*(prime-1))))
          _ = _phi([self.x,self.y])
          return ECFP4(_[0],_[1])
      def glsMulG2(self,a):
         # Faster multiplication for Torsion Points from G2
         return _GLSPointMulG2(a,self)
      def copy(self):return ECFP4(self.x,self.y,torsion=self.istorsion)
      def pickRandomPoint():
          _ = _swumapping(ECFP4.field.pickrandom())
          return ECFP4(_[0],_[1])
      def pickTorsionPoint():
         _ = _cleancofactor(ECFP4.pickRandomPoint())  # Cofactor cleaning of a random point
         _.istorsion=True
         return _
      def pickRandomScalar(): 
            return gmp.mpz(random.randint(0, (ECFP4.r ^ (1 << (ECFP4.r.bit_length() - 1)))) | (1 << (ECFP4.r.bit_length() - 1)) )
      def hashtoG2(identifier,mode=0):
          #     mode=0: Encode to Curve (NU-encode-to-curve), mode=1: Random Oracle model (RO-hash-to-curve)
          #     https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-06#name-roadmap 
          if mode == 0:
               _hf = HashToField(identifier,_basefield,extdegree=4,count=1)
               _ = _swumapping(ECFP4.field([gmp.mpz(_hf[0][0]),gmp.mpz(_hf[0][1]),gmp.mpz(_hf[0][2]),gmp.mpz(_hf[0][3])]))   
               _ = _cleancofactor(ECFP4(_[0],_[1]))
               _.istorsion = True      
               return _
          else:
               _hf = HashToField(identifier,_basefield,extdegree=4,count=2)
               _1 = _swumapping(ECFP4.field([gmp.mpz(_hf[0][0]),gmp.mpz(_hf[0][1]),gmp.mpz(_hf[0][2]),gmp.mpz(_hf[0][3])]))         
               _2 = _swumapping(ECFP4.field([gmp.mpz(_hf[1][0]),gmp.mpz(_hf[1][1]),gmp.mpz(_hf[1][2]),gmp.mpz(_hf[1][3])]))         
               _1,_2 = _add(_1[0],_1[1],_2[0],_2[1])
               _ = _cleancofactor(ECFP4(_1,_2))
               _.istorsion = True
               return _                   
      def isOnCurve(self):
         return self.y**2 == (self.x**3) + ECFP4.B
      def isTorsion(self):
         # Check if a point P is a Torsion Point
         # According to https://eprint.iacr.org/2019/814.pdf we have to check that  u*ψ3(P)-ψ2(P)+P="Infinity"
         # Or with according to https://hackmd.io/@yelhousni/bls12_subgroup_check that :−z⋅ψ(ϕ(Q))+ϕ(Q)+Q="Infinity" when  ϕ(P) is the endomorphisme of G2 (w*x,y)
         # However, all theses are equivalents to check that u*P=ψ(P) (we can show that ψ4(P)-ψ(P)+P="Infinity" for every point on the curve)
         # Same hint pointed by Scott :https://eprint.iacr.org/2021/1130.pdf
         self.istorsion = False
         self.istorsion =(_u * self == self.phi())
         return self.istorsion
      def toBytes(p):
         #     Point compression/Serialization as described by ZCach serialization format
         #     https://www.ietf.org/archive/id/draft-irtf-cfrg-pairing-friendly-curves-11.html#name-zcash-serialization-format-
         C_bit,I_bit,S_bit = 1,int(p.infinity),0 if p.infinity else int(FpMsgn0(p.y,_basefield) > 0)
         m_byte = C_bit << 7 | I_bit << 6 | S_bit << 5
         x_string = I2OSP(0,_sizeInBytes << 2) if p.infinity else I2OSP(p.x._raw[0],_sizeInBytes) + I2OSP(p.x._raw[1],_sizeInBytes) \
                     + I2OSP(p.x._raw[2],_sizeInBytes) + I2OSP(p.x._raw[3],_sizeInBytes)
         return bytes([m_byte])+x_string[0:]
      def fromBytes(bytearray):
               #     Point de-compression/de-Serialization as described by ZCach serialization format
               #     https://www.ietf.org/archive/id/draft-irtf-cfrg-pairing-friendly-curves-11.html#name-zcash-serialization-format-
               if (m_byte:=bytearray[0] & 0xE0)==0xE0:raise TypeError("Invalide compressed point format ...")
               bytearray = bytearray[1:]
               if (m_byte & 0x80 == 0) or(len(bytearray)!=_sizeInBytes<<2):raise TypeError("Invalide compressed point format ...")   # Only point's compression format is implemented
               if (m_byte & 0x40 != 0):
                  if (any([e != 0 for e in bytearray])): raise TypeError("Invalide compression of an infinity point ...")
                  else :return ECFP4(None)
               else:
                  x = ECFP4.field([OS2IP(bytearray[:_sizeInBytes]),OS2IP(bytearray[_sizeInBytes:_sizeInBytes<<1]),\
                                 OS2IP(bytearray[_sizeInBytes<<1:_sizeInBytes*3]),OS2IP(bytearray[_sizeInBytes*3:_sizeInBytes << 2])])
                  y = (x**3 + ECFP4.B).sqrt()
                  if y is None:raise TypeError("Invalide point: not in the curve ...")
                  else:
                     if int(FpMsgn0(y,_basefield)>0) == int(m_byte & 0x20!=0):return ECFP4(x,y)
                     else :return ECFP4(x,-y)
      def toBase64(self):
            return base64.b64encode(self.toBytes()).decode("ascii")
      def fromBase64(str):
            return ECFP4.fromBytes(base64.b64decode(str))
                     
   _basefield = CurveParams["p"]
   _sizeInBytes = (_basefield.bit_length() // 8) + int(_basefield.bit_length() % 8 != 0)
   ECFP4.field = Extf.F4(CurveParams)
   ECFP4.B = ECFP4.field(CurveParams["Btw"])
   ECFP4.r = CurveParams["r"]
   ECFP4.u = CurveParams["u"]
   _u = CurveParams["u"]
   _frobConsts = CurveParams["frobConsts"]
      #      Parametres of the constant-time Hash to G2 (swu+Isogeny)
   _swuZ = ECFP4.field(CurveParams["swuParamsG2"]["Z"])
   _swuA = ECFP4.field(CurveParams["swuParamsG2"]["swuA"])
   _swuB = ECFP4.field(CurveParams["swuParamsG2"]["swuB"])
   _BdivA = -_swuB / _swuA
   _invZ = -1 / _swuZ
   _Xnum = [ECFP4.field(i) for i in CurveParams["swuParamsG2"]["Xnum"]]
   _Ynum = [ECFP4.field(i) for i in CurveParams["swuParamsG2"]["Ynum"]]
   _Yden = [ECFP4.field(i) for i in CurveParams["swuParamsG2"]["Yden"]]
   _Xden = [ECFP4.field(i) for i in CurveParams["swuParamsG2"]["Xden"]]
   return ECFP4

#--------------------------------------------------------------------------------------------------------------------------------------------------------------------#
# Elliptic Curves implementation Over Fp8:
#                  - Affine coordinates implementation (field inversion is sufficently fast on gmp) 
#                  - SWU points mapping using isogenies
#                  - GLS Multuplication for Torsion points in G2
#                  - Sliding window multiplication for points not in G2 (in E(Fp4))
#                  - Constant-time implementation
#--------------------------------------------------------------------------------------------------------------------------------------------------------------------#
def ECFP8(CurveParams):
   _add    =  lambda x1,y1,x2,y2:[(_1:=((_0:=((y2-y1)/(x2-x1)))**2-x2-x1)),(_0*(x2-_1)-y2)]
   _double =  lambda x,y:[(_1:=((_0:=((3*x**2)/(2*y)))**2-2*x)),(_0*(x-_1)-y)] 

   def _swumapping(u):
      #     Simplified Shallue-van de Woestijne-Ulas Method (Simplified SWU for AB == 0)
      #     https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-05#section-6.6.3
      #     https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-05#appendix-C.3
      t1 = _swuZ * u**2
      t2 = t1**2
      x1 = (t1 + t2).inverse()
      if x1 == 0: x1 = _invZ
      else : x1 = x1 + 1
      x1 = x1 * _BdivA
      gx1 = (x1**2 + _swuA) * x1 + _swuB
      y = gx1.sqrt()
      if not (y is None): 
         if FpMsgn0(u,_basefield) != FpMsgn0(y,_basefield):y = -y
         x = x1
      else:
         x2 = t1 * x1
         t2 = t1 * t2
         gx2 = gx1 * t2
         y = gx2.sqrt()
         if FpMsgn0(u,_basefield) != FpMsgn0(y,_basefield):y = -y
         x = x2
      # isogeny map from E' to E "Wahby and Boneh" https://eprint.iacr.org/2019/403
      x_num,x_den,y_num,y_den = _Xnum[0],_Xden[0],_Ynum[0],_Yden[0]
      powx = x
      for i in range(1,len(_Ynum)):
         y_num = (y_num + _Ynum[i] * powx)
         y_den = (y_den + _Yden[i] * powx)
         if i < len(_Xnum):
            x_num = (x_num + _Xnum[i] * powx)
            x_den = (x_den + _Xden[i] * powx)
         powx = powx * x
      return  [x_num / x_den,y * (y_num / y_den)]
  # Phi()  optimized endomorphisme to be used for cleaning cofactor 
  # Initiallly Phi is obteined by multiplying Fp8 constantes wwith frobinus of x and y
   def _phi(x):
     return [ECFP8.field([2 * _frobConsts[9] * (x[0]._raw[3]),2 * _frobConsts[9] * x[0]._raw[2],-_frobConsts[8] * x[0]._raw[0],_frobConsts[8] * x[0]._raw[1],\
                          _frobConsts[7] * (x[0]._raw[4] - x[0]._raw[5]),-_frobConsts[7] * (x[0]._raw[5] + x[0]._raw[4]),(x[0]._raw[6]) * (_frobConsts[5] + 1),\
                          -(x[0]._raw[7]) * (_frobConsts[5] + 1)]),\
             ECFP8.field([-(x[1]._raw[6] - x[1]._raw[7]) * _frobConsts[17],(x[1]._raw[6] + x[1]._raw[7]) * _frobConsts[17],-(x[1]._raw[5] + x[1]._raw[4]) * \
                          _frobConsts[16],(x[1]._raw[5] - x[1]._raw[4]) * _frobConsts[16],-x[1]._raw[2] * _frobConsts[14],x[1]._raw[3] * _frobConsts[14],\
                          -x[1]._raw[1] * _frobConsts[15],-x[1]._raw[0] * _frobConsts[15]])]
  # Phi8()  endomorphisme of order 8 to be used for cleaning cofactor
   def _phi8(x):
     return [ECFP8.field([x[0]._raw[0] * _frobConsts[5] ,x[0]._raw[1] * _frobConsts[5] ,x[0]._raw[2] * _frobConsts[5] ,x[0]._raw[3] * _frobConsts[5] , \
             x[0]._raw[4] * _frobConsts[5] ,x[0]._raw[5] * _frobConsts[5] ,x[0]._raw[6] * _frobConsts[5] ,x[0]._raw[7] * _frobConsts[5] ]),-x[1]]
   def _phi4(x):
     _mulbyu =lambda x:ECFP8.field([-x._raw[1],x._raw[0],-x._raw[3],x._raw[2],-x._raw[5],x._raw[4],-x._raw[7],x._raw[6]])
     return [ECFP8.field([x[0]._raw[0] * (_frobConsts[5] + 1) ,x[0]._raw[1] * (_frobConsts[5] + 1) ,x[0]._raw[2] * (_frobConsts[5] + 1) ,x[0]._raw[3] * \
            (_frobConsts[5] + 1) , -x[0]._raw[4] * (_frobConsts[5] + 1) ,-x[0]._raw[5] * (_frobConsts[5] + 1) ,-x[0]._raw[6] * (_frobConsts[5] + 1) ,\
            -x[0]._raw[7] * (_frobConsts[5]+1) ]),(-_mulbyu(x[1].conjugate()))]  # Frobinus at order 4 is just a conjugate !
  # Inverse of endomorphisme to be used for optimizing cleaning cofator
  # Initiallly InvPhi is obteined by multiplying Fp8 constantes wwith frobinus of x and y
  #   def _invPhi(x):return ECFP8((x.x*_invPhic1).invfrobinus(),(x.y*_invPhic2).invfrobinus())
   def _invPhi(P):
     return ECFP8(ECFP8.field([-2 * _frobConsts[4] * P.x._raw[2],2 *_frobConsts[4] * P.x._raw[3],-_frobConsts[3] * P.x._raw[1],-_frobConsts[3] * P.x._raw[0],\
            (P.x._raw[5] - P.x._raw[4]) * _frobConsts[6],(P.x._raw[4] + P.x._raw[5]) * _frobConsts[6],-_frobConsts[5] * P.x._raw[6],_frobConsts[5] * P.x._raw[7]]),
            ECFP8.field([-_frobConsts[22] * P.y._raw[7],-_frobConsts[22] * P.y._raw[6],-_frobConsts[17] * P.y._raw[4],_frobConsts[17] * P.y._raw[5],\
            _frobConsts[15] * (P.y._raw[3] + P.y._raw[2]),_frobConsts[15] * (P.y._raw[2] - P.y._raw[3]),_frobConsts[23] * (P.y._raw[0] - P.y._raw[1]),\
            -_frobConsts[23] * (P.y._raw[0] + P.y._raw[1])]))
   def _GLSPointMulG2(a,P):
      #     GLS Implementation of points multiplication on G2 for the BLS48 Curve (16-GLS)
      #     Inspired from Joppe W. Bos, Craig Costello, and Michael Naehrig https://eprint.iacr.org/2013/458.pdf
      #     Constant-Time multiplication for elements in G2
      #     Point's operations are performent using affine coordinates
      code = Recs._recordScalarGLS16(a,abs(_u),ECFP8.r) 
      P1 = _phi([P.x,P.y])
      P2 = _phi(P1)
      P3 = _phi(P2)
      sig_u = abs(_u+1) - abs(_u)
      T1 = [[P.x,P.y]]
      T1 = T1 + [_add(P1[0],sig_u * P1[1],T1[0][0],T1[0][1])]
      T1 = T1 + [_add(P2[0],P2[1],T1[0][0],T1[0][1])] 
      T1 = T1 + [_add(P2[0],P2[1],T1[1][0],T1[1][1])]
      T1 = T1 + [_add(P3[0],sig_u * P3[1],T1[0][0],T1[0][1])]
      T1 = T1 + [_add(P3[0],sig_u * P3[1],T1[1][0],T1[1][1])]
      T1 = T1 + [_add(P3[0],sig_u * P3[1],T1[2][0],T1[2][1])]
      T1 = T1 + [_add(P3[0],sig_u * P3[1],T1[3][0],T1[3][1])]
      T2 = [_phi4(i) for i in T1]
      T3 = [_phi4(i) for i in T2]
      T4 = [_phi4(i) for i in T3]
      out_sig = (1 - ((code & 1) << 1))
      code = code >> 1
      c1, c2, c3, c4  = code & 15, (code >> 4) & 15 ,(code >> 8) & 15, (code >> 12) & 15
      s1, s2, s3, s4  = ((c1 & 1) << 1) - 1 , ((c2 & 1) << 1) - 1 , ((c3 & 1) << 1) - 1, ((c4 & 1) << 1) - 1
      _1 = _add(T1[c1 >> 1][0], s1 * T1[c1 >> 1][1], T2[c2 >> 1][0], s2 * T2[c2 >> 1][1])
      _2 = _add(T3[c3 >> 1][0], s3 * T3[c3 >> 1][1], T4[c4 >> 1][0], s4 * T4[c4 >> 1][1])
      res = _add(_1[0], _1[1], _2[0],_2[1])
      code = code >> 16
      while (code != 1):
         res = _double(res[0], res[1]) 
         c1, c2, c3, c4  = code & 15, (code >> 4) & 15 ,(code >> 8) & 15, (code >> 12) & 15
         s1, s2, s3, s4  = ((c1 & 1) << 1) - 1 , ((c2 & 1) << 1) - 1 , ((c3 & 1) << 1) - 1, ((c4 & 1) << 1) - 1
         _1 = _add(T1[c1 >> 1][0], s1 * T1[c1 >> 1][1], T2[c2 >> 1][0], s2 * T2[c2 >> 1][1])
         _2 = _add(T3[c3 >> 1][0], s3 * T3[c3 >> 1][1], T4[c4 >> 1][0], s4 * T4[c4 >> 1][1])
         _3 = _add(_1[0], _1[1], _2[0], _2[1])
         res = _add(res[0], res[1], _3[0], _3[1])
         code = code >> 16
      return ECFP8(res[0],out_sig * res[1])
   def _cleancofactor(P):
    # Fast way to clean Cofactor of G2 using Endomorphisme
    # using "Budroni-Pintore" approach (https://ia.cr/2017/419).
    # Optimlized personaly using inversed endomorphisme
      _ = _phi8([P.x,P.y])
      P8 = ECFP8(_[0],_[1])
      xP = (_u - 1) * _invPhi(P8)
      _ = 2 * P8 - P + xP
      for i in range(7):
         xP = _u * _invPhi(xP)
         _ = _ + xP
      return _

   class ECFP8 :
      def __init__(self,x,y = None,dotest = False,torsion = False):
         self.istorsion = torsion
         if x is None:
            self.infinity = True
         else:
            if y is None:
              self.x = x if type(x) == ECFP8.field else ECFP8.field(x)
              _ = (x**3 + ECFP8.B).sqrt()
              if not(_ is None):self.infinity,self.y,self.z = False,_,ECFP8.field([1,0,0,0,0,0,0,0])
              else :raise TypeError("Invalide curve point parametres ...")
            else:
              self.x = x if type(x) == ECFP8.field else ECFP8.field(x)
              self.y = y if type(x) == ECFP8.field else ECFP8.field(y)
              self.z = ECFP8.field([1,0,0,0,0,0,0,0])
              self.infinity = False
              if (dotest) and (not(y.sqr() == (x**3 + ECFP8.B))):raise TypeError("Invalide curve point parametres ...")
      def __str__(self):return "("+str(self.x) + " , "+str(self.y)+")" if not self.infinity else "Infinity"
      __repr__ = __str__
      def __add__(self,q):
        if self.infinity:
           if q.infinity:return ECFP8(None)
           else : return q.copy()
        else:
           if q.infinity:return self.copy()
           else:
            if self.x == q.x:
               if self.y == q.y:
                  _res = _double(self.x, self.y)
                  return ECFP8(_res[0],_res[1])
               else: return ECFP8(None)
            else:
               _res = _add(self.x, self.y, q.x, q.y)
               return ECFP8(_res[0],_res[1])
      def __neg__(self):return ECFP8(self.x, -self.y)
      def __sub__(self,q):return self +(-q)
      def __eq__(self,q): return (self.x == q.x) and (self.y == q.y) if not(self.infinity | q.infinity) else (self.infinity == q.infinity)
      def __ne__(self,q): return (self.infinity != q.infinity) or (self.x != q.x) or (self.y != q.y)
      def __rmul__(self,b):
            # Constant-time multiplication using w-sliding window (w=3)
            # Faster than Montgomery Ladder, use affine coordinates                           
            if (type(b) != int) & (type(b) != gmp.mpz) : 
                  raise TypeError("Invalide scalar value for multiplication ...")
            else :
               _outSig = abs(b+1) - abs(b)
               b = abs(b) % ECFP8.r
               if (self.istorsion) and (b.bit_length()>(ECFP8.r.bit_length()>>4)): return _GLSPointMulG2(b,self)
               else :
                  if self.infinity: return ECFP8(None)
                  if b==0 :return ECFP8(None)
                  if b==2 :return ECFP8((res:=_double(self.x,self.y))[0], _outSig * res[1])
                  else:
                     T = [_double(self.x, self.y)] + [[self.x, self.y]]
                     T = T + [_add(T[0][0], T[0][1], self.x, self.y)]
                     T = T + [_add(T[0][0], T[0][1], T[2][0], T[2][1])]
                     T = T + [_add(T[0][0], T[0][1], T[3][0], T[3][1])]
                     _code = Recs._recordOneScalar(b + (b & 1) + 1)               
                     _aP   = T[(_code & (Recs._wMask >> 1)) + 1]+[1]                
                     _code = _code >> (Recs._wSize-1)
                     while (_code != 1):
                              _sig = 2 * (_code & 1)-1
                              _idx = ((_code & Recs._wMask) >> 1) + 1
                              _aP  = _double(_aP[0], _aP[1])
                              _aP  = _double(_aP[0], _aP[1])
                              _aP  = _double(_aP[0], _aP[1])
                              _aP  = _add(_aP[0], _aP[1], T[_idx][0], _sig * T[_idx][1])
                              _code =  _code >> Recs._wSize
                     _aP  = _add(_aP[0], _aP[1], T[1 - (b & 1)][0], -T[1 - (b & 1)][1])
                     return ECFP8(_aP[0] , _outSig * _aP[1])         
      def phi(self):
         #  Endomorphisme Phi(P)=u*P: Twist->Frobinus->Un-twist (in M-Type Mode for BLS48)
         #  Twist : (x,y)->(x/z^2,y/z^3)
         #  Frobinus :(x,y)->(x^P,y^P)
         #  Un-Twist : (x,y)->(x*z^2,y*z^3)
         #  Combinaison of the three maps is equivalent to one multiplication by Fp8 constants
         #  Multiplication by the Fp8 Constant can be converted to multiplication in the base field since this constante is sparse (and combined with the frobinus in the same operation).
         _ = _phi([self.x,self.y])
         return ECFP8(_[0],_[1])
      def glsMulG2(self,a):
         # Faster multiplication for Torsion Points from G2
         return _GLSPointMulG2(a,self)
      def copy(self):return ECFP8(self.x,self.y,torsion=self.istorsion)
      def pickRandomPoint():
          _ = _swumapping(ECFP8.field.pickrandom())
          return ECFP8(_[0],_[1])
      def pickTorsionPoint():
          _ = _cleancofactor(ECFP8.pickRandomPoint()) # Cofactor cleaning of a random point
          _.istorsion = True
          return _
      def pickRandomScalar(): 
            return gmp.mpz(random.randint(0, (ECFP8.r ^ (1 << (ECFP8.r.bit_length() - 1)))) | (1 << (ECFP8.r.bit_length() - 1)) )
      def hashtoG2(identifier,mode = 0):
          #     mode=0: Encode to Curve (NU-encode-to-curve), mode=1: Random Oracle model (RO-hash-to-curve)
          #     https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-06#name-roadmap
          if mode == 0:
               _hf = HashToField(identifier,_basefield,extdegree = 8,count = 1)
               _ = _swumapping(ECFP8.field([gmp.mpz(i) for i in _hf[0]]))
               _ = _cleancofactor(ECFP8(_[0],_[1]))
               _.istorsion = True
               return _
          else:
               _hf = HashToField(identifier,_basefield,extdegree = 8,count = 2)
               _1 = _swumapping(ECFP8.field([gmp.mpz(i) for i in _hf[0]]))
               _2 = _swumapping(ECFP8.field([gmp.mpz(i) for i in _hf[1]]))
               _1,_2 = _add(_1[0],_1[1],_2[0],_2[1])
               _ = _cleancofactor(ECFP8(_1,_2))
               _.istorsion = True
               return _
      def isOnCurve(self):
         return self.y**2 == (self.x**3) + ECFP8.B
      def isTorsion(self):
         # Check if a point P is a Torsion Point
         # According to https://eprint.iacr.org/2019/814.pdf we have to check that  u*ψ3(P)-ψ2(P)+P="Infinity"
         # Or with according to https://hackmd.io/@yelhousni/bls12_subgroup_check that :−z⋅ψ(ϕ(Q))+ϕ(Q)+Q="Infinity" when  ϕ(P) is the endomorphisme of G2 (w*x,y)
         # However, all theses are equivalents to check that u*P=ψ(P) (we can show that ψ4(P)-ψ(P)+P="Infinity" for every point on the curve)
         # Same hint pointed by Scott :https://eprint.iacr.org/2021/1130.pdf
         self.istorsion = False
         self.istorsion = (_u * self == self.phi())
         return self.istorsion
      def toBytes(p):
         #     Point compression/Serialization as described by ZCach serialization format
         #     https://www.ietf.org/archive/id/draft-irtf-cfrg-pairing-friendly-curves-11.html#name-zcash-serialization-format-
         C_bit,I_bit,S_bit = 1,int(p.infinity),0 if p.infinity else int(FpMsgn0(p.y,_basefield) > 0)
         m_byte = C_bit << 7 | I_bit << 6 | S_bit << 5
         if p.infinity:x_string = I2OSP(0,_sizeInBytes << 2)
         else:
            x_string = I2OSP(p.x._raw[0],_sizeInBytes) + I2OSP(p.x._raw[1],_sizeInBytes) + I2OSP(p.x._raw[2],_sizeInBytes) + I2OSP(p.x._raw[3],_sizeInBytes) +\
                     I2OSP(p.x._raw[4],_sizeInBytes) + I2OSP(p.x._raw[5],_sizeInBytes) + I2OSP(p.x._raw[6],_sizeInBytes) + I2OSP(p.x._raw[7],_sizeInBytes)
         return bytes([m_byte])+x_string[0:]

      def fromBytes(bytearray):
               #     Point de-compression/de-Serialization as described by ZCach serialization format
               #     https://www.ietf.org/archive/id/draft-irtf-cfrg-pairing-friendly-curves-11.html#name-zcash-serialization-format-
               if (m_byte := bytearray[0] & 0xE0) == 0xE0:raise TypeError("Invalide compressed point format ...")
               bytearray = bytearray[1:]
               if (m_byte & 0x80 == 0) or (len(bytearray) != _sizeInBytes<<3):raise TypeError("Invalide compressed point format ...")  # Only point's compression format is implemented
               if (m_byte & 0x40 != 0):
                  if (any([e != 0 for e in bytearray])): raise TypeError("Invalide compression of an infinity point ...")
                  else :return ECFP8(None)
               else:
                  x = ECFP8.field([OS2IP(bytearray[:_sizeInBytes]),OS2IP(bytearray[_sizeInBytes:_sizeInBytes << 1]),OS2IP(bytearray[_sizeInBytes << 1:_sizeInBytes * 3]),\
                                 OS2IP(bytearray[_sizeInBytes * 3:_sizeInBytes << 2]),OS2IP(bytearray[_sizeInBytes << 2:_sizeInBytes * 5]),OS2IP(bytearray[_sizeInBytes * 5:_sizeInBytes * 6]),\
                                 OS2IP(bytearray[_sizeInBytes * 6:_sizeInBytes * 7]),OS2IP(bytearray[_sizeInBytes * 7:_sizeInBytes * 8])  ])
                  y = (x**3 + ECFP8.B).sqrt()
                  if y is None:raise TypeError("Invalide point: not in the curve ...")
                  else:
                     if int(FpMsgn0(y,_basefield)>0) == int(m_byte & 0x20 != 0):return ECFP8(x,y)
                     else :return ECFP8(x,-y)
      def toBase64(self):
            return base64.b64encode(self.toBytes()).decode("ascii")
      def fromBase64(str):
            return ECFP8.fromBytes(base64.b64decode(str))

   _basefield = CurveParams["p"]
   _sizeInBytes = (_basefield.bit_length() // 8) + int(_basefield.bit_length() % 8 != 0)
   ECFP8.field = Extf.F8(CurveParams)
   _u = CurveParams["u"]  
   _frobConsts = CurveParams["frobConsts"]
   #   Parametres of the constant-time Hash to G2 (swu+Isogeny)
   _swuZ = ECFP8.field(CurveParams["swuParamsG2"]["Z"])
   _swuA = ECFP8.field(CurveParams["swuParamsG2"]["swuA"])
   _swuB = ECFP8.field(CurveParams["swuParamsG2"]["swuB"])
   _BdivA = -_swuB/_swuA
   _invZ = -1/_swuZ
   _Xnum = [ECFP8.field(i) for i in CurveParams["swuParamsG2"]["Xnum"]]
   _Ynum = [ECFP8.field(i) for i in CurveParams["swuParamsG2"]["Ynum"]]
   _Yden = [ECFP8.field(i) for i in CurveParams["swuParamsG2"]["Yden"]]
   _Xden = [ECFP8.field(i) for i in CurveParams["swuParamsG2"]["Xden"]]
   ECFP8.B = ECFP8.field(CurveParams["Btw"])
   ECFP8.u = _u
   ECFP8.r = CurveParams["r"]
   return ECFP8