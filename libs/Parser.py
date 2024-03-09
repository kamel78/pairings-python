import re
from itertools import chain

class FieldsParser:
    roots=['u','v','w','z','t','x'] 
    def __init__(self,_tower):
        for i in _tower:
            if (i!=2)&(i!=3):raise TypeError("Invalid extension tower : "+str(_tower)+"....")    
        self.tower=_tower
        self._fieldcoefs=self._getcoefs(_tower) 
        self.degree=1
        for i in self.tower:self.degree*=i        
    def _getprefixed(self,expr):
        precedences = { '*': 3,'+': 2,'(': 1,}
        def listtotree(list):
            def tree(_list,id):
                if _list[id] in['+','*']:
                    operand1,id1=tree(_list,id+1)
                    operand2,id2=tree(_list,id1)
                    return [_list[id],operand1,operand2],id2
                else:return [_list[id]],id+1
            return tree(list,0)[0]
        expr=expr.replace(" ","").replace("\n","").replace("\r","")
        for i in self.roots:expr=expr.replace(i+'^2',i.upper())
        for i in self.roots:
            expr=expr.replace('('+i,'(1*'+i).replace('(*'+i+'*',i+'*')
            expr=expr.replace('('+i.upper(),'(1*'+i.upper())
            expr=expr.replace('+'+i,'+1*'+i).replace('1*'+i+'*',i+'*')
            expr=expr.replace('+'+i.upper(),'+1*'+i.upper()).replace('1*'+i.upper()+'*',i.upper()+'*')
        if expr[0]in self.roots+[i.upper() for i in self.roots]:expr=('1*'+expr).replace('1*'+expr[0]+'*',expr[0]+'*')
        tokens = re.findall(r"(\b\w*[\.]?\w+\b|[\(\)\+\*\-\/])", expr)
        stack,postfix = [],[]
        try:
            for token in tokens:
                if token.isalnum():postfix.append(token)
                elif token == '(':stack.append(token)
                elif token == ')':
                    top = stack.pop()
                    while top != '(':
                        postfix.append(top)                   
                        top = stack.pop()
                else:
                    while stack and (precedences[stack[-1]] >= precedences[token]):postfix.append(stack.pop())
                    stack.append(token)
        except:raise TypeError(" incorrect input expression .. ")  
        while stack:
                postfix.append(stack.pop())
        _list=list(reversed([i for i in re.split("([+-/*() uvwzUVWZ])", ' '.join(postfix)) if ((i!="")&(i!=" "))]))
        return listtotree(_list)
    #------------------------------------------------------------------------------------------------------------------#
    def _getdevelopped(self,param):
        if len(param)==1:return [param[0]]  
        else:
            match param[0]:
                case '*':
                    if param[1][0] in self._fieldcoefs:_root,_param =param[1][0],param[2]
                    else:_root,_param=param[2][0],param[1]
                    match _param[0]:
                        case '*':
                            if _param[1][0] in self._fieldcoefs:__root,__param=_param[1][0],_param[2]
                            else:__root,__param=_param[2][0],_param[1]             
                            return self._getdevelopped(['*',[__root[0]+_root],__param])
                        case '+':
                            return ['+',self._getdevelopped(['*',[_root],_param[1]]),self._getdevelopped(['*',[_root],_param[2]])]
                        case _:
                            return param
                case '+':
                    return ['+',self._getdevelopped(param[1]),self._getdevelopped(param[2])]     
                case _ :
                    return param
    #------------------------------------------------------------------------------------------------------------------#
    def _getlinearised(self,param):
        if len(param)==1:return param[0]
        else:
            match param[0]:
                case '+':return [self._getlinearised(param[1]),self._getlinearised(param[2])]
                case _: 
                    if param[1][0] in self._fieldcoefs:return [self._getlinearised(param[2]),'*',self._getlinearised(param[1])]  
                    else :return [self._getlinearised(param[1]),'*',self._getlinearised(param[2])] 
    #------------------------------------------------------------------------------------------------------------------#
    def _getflattened(self,param):
        if type(param)!=list:return [[param,'']]
        else: 
            match len(param):
                case 3:return [[param[0],param[2]]]
                case 2:return self._getflattened(param[0])+self._getflattened(param[1])
                case _:return [[param,'']]
    #------------------------------------------------------------------------------------------------------------------#
    def _getexistantcoefs(self,param):
        return self._getflattened(self._getlinearised(self._getdevelopped(self._getprefixed(param))))
    #------------------------------------------------------------------------------------------------------------------#
    def _getcoefs(self,tower,_roots=roots):
        _coefs=list(chain(*[_roots[i] if (tower[i]==2) else (_roots[i],_roots[i].upper()) for i in range(0,len(tower))]))
        _=[''.join([_coefs[j] for j in range(len(_coefs)) if (i & (1 << j))]) for i in range(1 << len(_coefs))]
        _=[i for i in _  if len([j for j in [i+i.upper() for i in _coefs] if j in i ])==0]
        return _     
    #------------------------------------------------------------------------------------------------------------------#
    def _getFieldInts(self,expr):
        _=[]
        exprpairs=self._getexistantcoefs(expr)           
        exprfields=[j[1] if j[1] in self._fieldcoefs else j[0]  for j in exprpairs]
        exprvals=[j[0] if j[1] in self._fieldcoefs else j[1]  for j in exprpairs]
        for i in exprfields:
            if not(i in self._fieldcoefs):raise TypeError(" Expression do not belong to the field Fp"+str(self.degree)+" ... ") 
        for i in self._fieldcoefs:
            id=exprfields.index(i) if i in exprfields else -1
            if id!=-1 :_.append(int(exprvals[id],0))
            else:_.append(0)
        return _ 
    #------------------------------------------------------------------------------------------------------------------#
    def parse(self,expr):
        return self._getFieldInts(expr)
    #------------------------------------------------------------------------------------------------------------------#
    def listtostring(self,list,tower,degrees,format="decimal"):    
        def tostr(a,_format):
            if _format=="decimal":return str(a)
            else :
                if _format=="hex":return hex(a)
                else :raise TypeError("Invalide conversion format  ..." )
        def tostring(x,_roots):
            match len(x):
                    case 2:
                        if x[0]==0:
                            if x[1]==0:return "" 
                            else: 
                                if x[1]==1:return _roots[0]
                                else: return tostr(x[1],format)+"*"+_roots[0]
                        else :
                            if x[1]==0: return tostr(x[0],format)
                            else :
                                if x[1]==1:return tostr(x[0],format)+" + "+_roots[0]
                                else: return tostr(x[0],format)+" + "+tostr(x[1],format)+"*"+_roots[0]                                                                
                    case 3:
                        if x[0]==0: 
                            if x[1]==0:
                                if x[2]==0:return ""
                                else : return tostr(x[2],format)+"*"+_roots[0]+"^2" if x[2]!=1 else _roots[0]+"^2"
                            else:
                                if x[2]==0:return tostr(x[1],format)+"*"+_roots[0] if x[1]!=1 else _roots[0]
                                else :return (tostr(x[1],format)+"*"+_roots[0] if x[1]!=1 else _roots[0])+" + "+(tostr(x[2],format)+"*"+_roots[0]+"^2" if x[2]!=1 else _roots[0]+"^2")                                
                        else :
                            if x[1]==0:
                                if x[2]==0: return  tostr(x[0],format)
                                else :return  tostr(x[0],format)+" + "+(tostr(x[2],format)+"*"+_roots[0]+"^2" if x[2]!=1 else _roots[0]+"^2")
                            else :
                                if x[2]==0:return tostr(x[0],format)+" + "+(tostr(x[1],format)+"*"+_roots[0] if x[1]!=1 else _roots[0])
                                else :         
                                    return tostr(x[0],format)+" + "+(tostr(x[1],format)+"*"+_roots[0] if x[1]!=1 else _roots[0])+" + "+(tostr(x[2],format)+"*"+_roots[0]+"^2" if x[2]!=1 else _roots[0]+"^2")                                    

                    case _:
                        idegree=degrees.index(len(x))
                        match tower[idegree]:
                            case 2:
                                mid=len(x)//2 
                                _1=tostring(x[:mid],_roots)
                                _2=tostring(x[mid:],_roots)
                                if _1=="":
                                    if _2=="": return ""
                                    else: return "("+_2+")*"+_roots[idegree] if _2!="1" else _roots[idegree]
                                else :
                                    if _2=="":return _1
                                    else :return _1+" + ("+_2+")*"+_roots[idegree] if _2!="1" else _1+" + "+_roots[idegree]                                   
                            case 3:
                                tid=len(x)//3   
                                _1=tostring(x[:tid],_roots)
                                _2=tostring(x[tid:tid*2],_roots)
                                _3=tostring(x[tid*2:],_roots)
                                if _1=="":
                                    if _2=="":
                                        if _3=="":return ""  
                                        else :return "("+_3+")*"+_roots[idegree]+"^2" if _3!="1" else _roots[idegree]+"^2"
                                    else:
                                        if _3=="":return "("+_2+")*"+_roots[idegree] if _2!="1" else _roots[idegree]
                                        else: return ("("+_2+")*"+_roots[idegree] if _2!="1" else _roots[idegree])+" + "+("("+_3+")*"+_roots[idegree]+"^2" if _3!="1" else +_roots[idegree]+"^2")
                                else:
                                    if _2=="":
                                        if _3=="":return _1
                                        else :return _1+" + "+("("+_3+")*"+_roots[idegree]+"^2" if _3!="1" else _roots[idegree]+"^2")
                                    else :
                                        if _3=="":return _1+" + "+("("+_2+")*"+_roots[idegree] if _2!="1" else _roots[idegree])
                                        else :return _1+" + "+("("+_2+")*"+_roots[idegree] if _2!="1" else _roots[idegree])+" + "+("("+_3+")*"+_roots[idegree]+"^2" if _3!="1" else _roots[idegree]+"^2")
        _=tostring(list,self.roots)
        return _ if _!="" else "0"        
    

    