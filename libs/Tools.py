import hashlib
import hmac
from random import randint

#---------------------------------------------------------------------------------------------------------------------------------------------------------
#   sgn0 "sign" of x: returns -1 if x is lexically larger than  -x and, else returns 1
#   https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-05#section-4.1
#---------------------------------------------------------------------------------------------------------------------------------------------------------
def FpMsgn0(x,p):
    thresh = (p - 1) // 2
    sign = 0
    for xi in reversed(x._raw):
        if xi > thresh:
            sign = -1 if sign == 0 else sign
        elif xi > 0:
            sign = 1 if sign == 0 else sign
    sign = 1 if sign == 0 else sign
    return sign

def Fpsgn0(x,p):
    thresh = (p - 1) // 2
    sign = 0
    if x > thresh:sign = -1 if sign == 0 else sign
    elif x > 0:sign = 1 if sign == 0 else sign
    sign = 1 if sign == 0 else sign
    return sign


#---------------------------------------------------------------------------------------------------------------------------------------------------------
#   I2OSP converts a nonnegative integer to an octet string of a specified length. RFC 3447, section 4.1 https://datatracker.ietf.org/doc/html/rfc3447#section-4.1
#---------------------------------------------------------------------------------------------------------------------------------------------------------
def I2OSP(x,length):
    if x < 0 or x >= (1 << (length<<3)):return None
    else :
        res=[0]*length
        for i in reversed(range(length)):
            res[i]=x & 0xFF
            x=x>>8
        return bytes(res)
#---------------------------------------------------------------------------------------------------------------------------------------------------------
#   OS2IP converts an octet string to a nonnegative integer. RFC 3447, section 4.2 https://datatracker.ietf.org/doc/html/rfc3447#section-4.2
#---------------------------------------------------------------------------------------------------------------------------------------------------------
def OS2IP(byts):
    res = 0
    for i in byts:res = (res << 8)+i
    return res

#---------------------------------------------------------------------------------------------------------------------------------------------------------
#   HMAC-based Extract-and-Expand Key Derivation Function (HKDF) https://datatracker.ietf.org/doc/html/rfc5869 
#---------------------------------------------------------------------------------------------------------------------------------------------------------
def HKDF_extract(inputkey, hashfunction,salt=None):
    if salt is None:salt = bytes((0,) * hashfunction().digest_size)
    return hmac.HMAC(salt, inputkey,hashfunction).digest()

def HKDF_expand(pseudorandomkey, keylength, hashfunction, info=b''):
    dsize = hashfunction().digest_size
    if len(pseudorandomkey) < dsize:raise ValueError("length of prk must be at least Hashlen")
    N = (keylength+ dsize - 1) // dsize
    if N == 0 or N > 255:raise ValueError("length arg to hkdf_expand cannot be longer than 255 * Hashlen")
    Ti = OKM = b''
    for i in range(N):
        Ti = hmac.HMAC(pseudorandomkey, Ti + info + I2OSP(i + 1, 1), hashfunction).digest()
        OKM += Ti
    return OKM[:keylength]

#---------------------------------------------------------------------------------------------------------------------------------------------------------
#   The expand_message_xmd function produces a pseudorandom byte string using a cryptographic hash function H that outputs b bits. 
#   https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-06#name-expand_message_xmd 
#---------------------------------------------------------------------------------------------------------------------------------------------------------
def Expand_Message_Xmd(message, DST, byteslength, hashfunction):   
    _xor = lambda str1, str2: bytes( s1 ^ s2 for (s1, s2) in zip(str1, str2) )
    if (ell:=(byteslength + hashfunction().digest_size - 1) // hashfunction().digest_size) > 255:
        raise ValueError("expand_message_xmd: ell=%d out of range" % ell)
    DST_prime = DST + I2OSP(len(DST), 1)
    Z_pad = I2OSP(0, hashfunction().block_size)
    l_i_b_str = I2OSP(byteslength, 2)
    b_0 = hashfunction(Z_pad + message + l_i_b_str + I2OSP(0, 1) + DST_prime).digest()
    b_vals = [None] * ell
    b_vals[0] = hashfunction(b_0 + I2OSP(1, 1) + DST_prime).digest()
    for i in range(1, ell):
        b_vals[i] = hashfunction(_xor(b_0, b_vals[i - 1]) + I2OSP(i + 1, 1) + DST_prime).digest()
    pseudo_random_bytes = b''.join(b_vals)
    return pseudo_random_bytes[0 : byteslength]

#---------------------------------------------------------------------------------------------------------------------------------------------------------
#   The hash_to_field function hashes a byte string msg of any length into one or more elements of a field F.
#   https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-06#name-hashing-to-a-finite-field 
#---------------------------------------------------------------------------------------------------------------------------------------------------------
def HashBytestoField(messagebytes, count, basefield, extdegree,DST=b''):
    L=round(((381) + 128) / 8) # parameter for 128bit level security
    byteslength = count * extdegree * L
    prngbytes = Expand_Message_Xmd(messagebytes, DST, byteslength,  hashlib.sha256)
    result = [None] * count
    for i in range(count):
        e_vals = [None] * extdegree
        for j in range(extdegree):
            elm_offset = L * (j + i * extdegree)
            tv = prngbytes[elm_offset : elm_offset + L]
            e_vals[j] = OS2IP(tv) % basefield
        result[i] = e_vals
    return result

def HashStringtoField(stringmsg,basefield,extdegree,count=1):
    return HashBytestoField(bytes(stringmsg,"UTF-8"),count,basefield,extdegree)

def HashToField(msg,basefield,extdegree,count=1):
    if type(msg)==str:return HashBytestoField(bytes(msg,"UTF-8"),count,basefield,extdegree)
    else: return HashBytestoField(msg,count,basefield,extdegree)