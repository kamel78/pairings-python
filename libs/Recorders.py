
_wSize  = 3
_wDSize = 2 * _wSize 
_wMask  = (1 << _wSize) - 1
_wDMask = (1 << _wDSize) - 1

# Scalar Recording for w-sliding multiplication algorithm
def _recordOneScalar(x):
      mu =  x.bit_length()      
      mu = mu + _wSize - (mu % _wSize)
      x =  x | (1 << mu)
      Code =  1
      while (x != 1):
            sign  = ((x >> (_wSize - 1)) & 2) - 1    
            Code  = (Code << _wSize) | ( (((x ^ sign) & _wMask) | 1) + (sign >> 1))
            x    =  x        >> _wSize 
      return Code >> 1

# Scalar recording for GLS-16 (for E(Fp8)) : 1st,4th,8th and 12th in {-1,1}, remaining sub-scalars in {-1,0,1} with alignement to the recorded ones
# Ensuring 1st,4th,8th and 12th sub-scalars are odd numbers using combination with "u"
def _recordScalarGLS16(a,u,r):
      _alpha = (u | (a % u)) & 1
      a = (r - a) * (1 - _alpha) + a * _alpha 
      decs=[_:=(a // u**i) % u for i in range(16)]
      _beta = (~decs[0] & 1) * (u & 1)      
      decs[0] = decs[0] + (_beta * u)
      i = 1
      while(decs[i]==0):
            decs[i] = u
            i=i+1
      decs[i] = decs[i] - _beta  
      for j in (4,8,12):
         _beta = (~decs[j] & 1)          
         decs[j-1] = decs[j-1] + (_beta * u)
         i = j
         while(decs[i]==0):
               decs[i] = u
               i=i+1
         decs[i] = decs[i] - _beta  
      mu=max([i.bit_length() for i in decs])
      decs[0] = (decs[0] >> 1) | (1 << mu)      
      decs[4] = (decs[4] >> 1) | (1 << mu)   
      decs[8] = (decs[8] >> 1) | (1 << mu)   
      decs[12] = (decs[12] >> 1) | (1 << mu)   
      for i in range(1,16):
         if (i % 4!=0):
            indic=-1
            while (indic!=0):
                  indic = (decs[i]  & ~decs[(i- (i % 4))]) & indic
                  indic = indic ^ (-indic)
                  decs[i] = decs[i] - indic
      code = 1
      while decs[0]!=0:
         _ = (decs[0] & 1)    
         decs[0] = decs[0] >> 1
         for i in range(1,len(decs)): 
               _ = _ |(((decs[i] & 1) << i) )
               decs[i] = decs[i] >> 1
         code = (code << 16) | _
      code = (code << 1) | (1 - _alpha)
      return code


# Scalar recording for GLS-8 (For E(Fp4)): first and fourth subscalar in {-1,1}, remaining sub-scalars in {-1,0,1} with alignement to the first/fourth  one
# Ensuring both first and  fourth sub-scalars are odd numbers using combination with "u"
def _recordScalarGLS8(a,u,r):
      _alpha = (u | (a % u)) & 1
      a = (r - a) * (1 - _alpha) + a * _alpha 
      decs=[_:=(a // u**i) % u for i in range(8)]
      _beta = (~decs[0] & 1) * (u & 1)      
      decs[0] = decs[0] + (_beta * u)
      i = 1
      while(decs[i]==0):
            decs[i] = u
            i=i+1
      decs[i] = decs[i] - _beta  
      _beta = (~decs[4] & 1)          
      decs[3] = decs[3] + (_beta * u)
      i = 4
      while(decs[i]==0):
            decs[i] = u
            i=i+1
      decs[i] = decs[i] - _beta             
      mu=max([i.bit_length() for i in decs])
      decs[0] = (decs[0] >> 1) | (1 << mu)      
      decs[4] = (decs[4] >> 1) | (1 << mu)   
      for i in range(1,8):
         if i!=4:
            indic=-1
            while (indic!=0):
                  indic = (decs[i]  & ~decs[i & 4]) & indic
                  indic = indic ^ (-indic)
                  decs[i] = decs[i] - indic      
      code =1
      while decs[0]!=0:
         _ = (decs[0] & 1)    
         decs[0] = decs[0] >> 1
         for i in range(1,len(decs)): 
               _ = _ |(((decs[i] & 1) << i) )
               decs[i] = decs[i] >> 1
         code = (code << 8) | _
      code = (code << 1) | (1 - _alpha)
      return code
   
# Scalar recording for GLS-4 (for E(Fp2)): first subscalar in {-1,1}, remaining sub-scalars in {-1,0,1} with alignement to the first one
def _recordScalarGLS4(a,u,r):
      _alpha = (u | (a % u)) & 1
      a = (r - a) * (1 - _alpha) + a * _alpha 
      decs=[_:=(a // u**i) % u for i in range(4)]
      _beta = (~decs[0] & 1) * (u & 1) 
      decs[0] = decs[0] + _beta * u
      if _beta ==1:
            i = 1
            while(decs[i]==0):
                  decs[i] = u
                  i=i+1
            decs[i] = decs[i] - _beta  
      mu=max([i.bit_length() for i in decs])
      decs[0] = (decs[0] >> 1) | (1 << mu)        
      for i in range(1,len(decs)):
         indic=-1
         while (indic!=0):
               indic = (decs[i]  & ~decs[0]) & indic
               indic = indic ^ (-indic)
               decs[i] = decs[i] - indic
      code =1
      while decs[0]!=0:
         _ = (decs[0] & 1)    
         decs[0] = decs[0] >> 1
         for i in range(1,len(decs)): 
               _ = _ |(((decs[i] & 1) << i) )
               decs[i] = decs[i] >> 1
         code = (code << 4) | _
      code = (code << 1) | (1 - _alpha)
      return code

# Scalar recording for GLV-2 : personalized recording according to Algorithm 12 from the paper: "Optimizing and securing GLV multiplication over BLS pairings-friendly curves".
def _recordScalarGLV2(scalar,lamda):
      x1 , x2 = scalar % lamda , scalar // lamda
      _beta = (~x1 & 1) * (lamda & 1)
      x1 = x1 + _beta * lamda
      x2 = x2 - _beta      
      mu = (x1 | abs(x2)).bit_length()
      mu = mu + _wDSize - (mu % _wSize)
      x1 = x1 | (1 << mu)   
      code =  1
      while (x1 != 1):
         sign = ((x1 >> _wSize) & 1) - 1                 
         even = ~x2 & 1                                  
         ai   = ((x1 ^ sign) |  1  ) & _wMask 
         bi   = ((x2 + sign) ^ sign) & _wMask
         di   =  ai - bi
         inc  = ((_wMask - (sign | 1) * di) & (bi + _wMask)) >> _wSize
         ai   = (ai - bi * even) & _wMask
         bi   =  di * even + bi
         inc  =  inc * even + ((even - 1) * sign)  
         code = (code << _wDSize) | (even + ((sign + 1) << 1) + (((ai >> 1) + ((bi - 1) << 1)) << 2))  
         x1   = (x1 >> _wSize) 
         x2   = (x2 >> _wSize) + inc
      return code