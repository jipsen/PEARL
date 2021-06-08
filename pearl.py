# PEARL: Implementing Correspondence Theory for Relevance Logic
# implementation by Peter Jipsen (jipsen@chapman.edu) 2021/02/16-05/19 (current version)
# in collaboration with Willem Conradie and Valentin Goranko

from IPython.display import display, Math

# Signature for input and output (the LaTeX symbols can be changed to agree with other conventions)
# Relevance logic symbols and corresponding Routley-Meyer frame symbols (prefixed by RM, only for output)
Meet="\\land";  Join="\\lor";   Himp="\\Rightarrow";  Coimp="\\coimp";        Eq="=";     Neq="\\neq"
Mult="\\circ";  Rimp="\\to";    Limp="\\leftarrow";   RMrel="R";              Top="\\top";Bot="\\bot"
Le="\\le";      RMle="\\preceq";RMnle="\\not\\preceq";Iden="\\mathbf t";      RMiden="O"; 
Invol="\\sim";Galcon="{\\sim^\\sharp}";             Dualgc="{\\sim^\\flat}";RMinvol="^*";

# First-order logic connectives and quantifiers (only for output)
And="\\land";   Or="\\lor";     Imp="\\implies";      Not="\\neg";      Iff="\\iff"
FALSE="\\text{False}";  TRUE="\\text{True}";               All="\\forall";   Exists="\\exists"

# can add further \newcommand macros in the string below
Macros=r"\newcommand{\coimp}{-\!\raisebox{.5pt}{\scriptsize<}\,}" 

VAR = set(["p","q","r"])|set("p_"+str(i) for i in range(10))
NOM = set(["\\mathbf i","\\mathbf j","\\mathbf k"])|set("\\mathbf j_"+str(i) for i in range(10))
CNOM = set(["\\mathbf m","\\mathbf n"])|set("\\mathbf n_"+str(i) for i in range(10))
ATOMS = VAR | NOM | CNOM # relevance logic variables, nominals and conominals
FVAR = set(["A","B","C","D","E","\\alpha","\\beta","\\gamma","\\chi","\\phi","\\psi","\\theta"])
VARFVAR = VAR | FVAR   # FVAR = formula variable
FOVAR = set(["u","v","w","x","y","z"])|set("x_"+str(i) for i in range(10))|set("y_"+str(i) for i in range(10))
FOINFIX = [(RMle,8),(RMnle,8),(Eq,8),(Neq,8),(And,5),(Or,5),(Imp,3),(Iff,2)]
FOPRE = [Not,RMrel,RMiden] #precedence 9
FOPOST = [RMinvol] #precedence 9
QUANT = [All,Exists] #precedence 9
CONST = set([Iden,Bot,Top,TRUE,FALSE])
NEG = [Invol,Galcon,Dualgc] #precedence 9
POSPOS = [(Meet,5),(Join,5),(Mult,7)]
PP0 = [t[0] for t in POSPOS]
NEGPOS = [(Rimp,3),(Imp,3),(Limp,3),(Le,1)]
NP0 = [t[0] for t in NEGPOS]
POSNEG = [(Coimp,3)]
PN0 = [t[0] for t in POSNEG]

################## Parser code (can ignore this) #################
# Terms are read using Vaughn Pratt's top-down parsing algorithm #

symbol_table = {}

def wrap(subt, t): # decide when to add parentheses during printing of terms
    return subt.tex() if subt.lbp > t.lbp or len(subt.a)<=1 else "("+subt.tex()+")"

class symbol_base(object):
    a = []
    def __repr__(self): 
        return self.tex()
    def tex(self):
        if len(self.a) == 0: return self.id
        if len(self.a) == 1: 
          if self.id[0]=="^": return wrap(self.a[0],self)+self.id
          return self.id+" "+wrap(self.a[0],self)
        if len(self.a) == 2: 
          return wrap(self.a[0],self)+self.id+(" " if self.id[0]=='\\' else "")+wrap(self.a[1],self)
        return self.id+" "+self.a[0].id+self.a[1].id+self.a[2].id

def symbol(id, bp=0): # identifier, binding power
    if id in symbol_table:
        s = symbol_table[id]    # look symbol up in table
        s.lbp = max(bp, s.lbp)  # update left binding power
    else:
        class s(symbol_base):   # create class for this symbol
            pass
        s.id = id
        s.lbp = bp
        s.nulld = lambda self: self
        symbol_table[id] = s
    return s

def advance(id=None):
    global token
    if id and token.id != id:
        raise SyntaxError("Expected "+id+" got "+token.id)
    token = next()

def nulld(self): # null denotation
    expr = expression()
    advance(")")
    return expr

def infix(id, bp):
    def leftd(self, left): # left denotation
        self.a = [left]
        self.a.append(expression(bp))
        return self
    symbol(id, bp).leftd = leftd

def prefix(id, bp):
    global token
    def nulld(self): # null denotation
        global token
        if token.id != "(":
            self.a = [expression(bp)]
            return self
        else:
            token = next()
            self.a = []
            if token.id != ")":
                while 1:
                    self.a.append(expression())
                    if token.id != ",":
                        break
                    advance(",")
            advance(")")
            return self
    symbol(id, bp).nulld = nulld

def postfix(id, bp):
    def leftd(self,left): # left denotation
        self.a = [left]
        return self
    symbol(id, bp).leftd = leftd

symbol("(").nulld = nulld
symbol(")")
symbol("[").nulld = nulld
symbol("]")
symbol("(end)")

for st in ATOMS|FVAR|FOVAR|CONST: symbol(st)
for st in NEG+FOPRE: prefix(st,9)
for st in FOPOST: postfix(st,9)
for st in FOVAR: prefix(All+" "+st,7)
for st in FOVAR: prefix(Exists+" "+st,7)
for t in POSPOS+NEGPOS+POSNEG+FOINFIX: infix(t[0],t[1])

def tokenize(st):
    i = 0
    while i<len(st):
        tok = st[i] #read single-letter token
        j = i+1
        if j<len(st) and st[j]=="_": #read subscript
          j+=1
          if st[j]=="{": j+=1
          while j<len(st) and st[j]>='0' and st[j]<='9': j+=1
          if j<len(st) and st[j]=="}": j+=1
          tok = st[i:j]
        elif tok=="{":
            tok = st[j]
            j+=1
        if tok=="\\": #read Latex symbol
            while j<len(st) and ((st[j]>='a' and st[j]<='z') or\
                (st[j]>='A' and st[j]<='Z')): j+=1
            if j<len(st) and st[j]=='^': #read \sim^\sharp, \sim^\flat
                j+=1
                if st[j]=='\\':
                    j+=1
                    while j<len(st) and ((st[j]>='a' and st[j]<='z') or\
                        (st[j]>='A' and st[j]<='Z')): j+=1
            if st[i]=="{" and st[j]=="}": j+=1
            tok = st[i:j]
            if tok in ["\\mathbf","\\forall","\\exists"]:
              j+=2
              if j<len(st) and st[j]=="_": #read subscript
                j+=1
                if st[j]=="{": j+=1
                while j<len(st) and st[j]>='0' and st[j]<='9': j+=1
                if j<len(st) and st[j]=="}": j+=1
              tok = st[i:j]
        i = j
        if tok!=' ':
            symb = symbol_table[tok]
            if not symb: raise SyntaxError("Unknown operator")
            yield symb()
    symb = symbol_table["(end)"]
    yield symb()

def expression(rbp=0):
    global token
    t = token
    token = next()
    left = t.nulld()
    while rbp < token.lbp:
        t = token
        token = next()
        left = t.leftd(left)
    return left

def parse(str): # e.g., t = parse(r"(p\circ q)\lor \mathbf t")
    global token, next
    next = tokenize(str.replace("{\\sim}","\\sim ")).__next__
    token = next()
    return expression()

output_list=[]

def showq(A, info=True): # display a quasi-inclusion
  global output_list
  if type(A)==str: st = A
  else: st = ",\\ ".join([repr(x) for x in A[:-1]])+\
             ("\\quad"+Imp+"\\quad " if len(A)>1 else "")+repr(A[-1])
  st = st.replace("\\sim","{\\sim}")
  output_list.append(st)
  if info==True:
    display(Math(Macros+st))

def show(A, info=True): # display a (list of) formula(s)
  global output_list
  st = A if type(A)==str else repr(A)
  st = st.replace("\\sim","{\\sim}")
  output_list.append(st)
  if info==True:
    display(Math(Macros+st))

############### end of parser code ##################


#Check if all occurances of a variable p in a formula A are positive/negative

def all_positive(A,p):
  if A.a==[]: return True
  if A.id in NEG: return all_negative(A.a[0],p)
  if A.id in PP0:
    return all_positive(A.a[0],p) and all_positive(A.a[1],p)
  if A.id in NP0:
    return all_negative(A.a[0],p) and all_positive(A.a[1],p)
  return "Error" # should not get here

def all_negative(A,p):
  if A.id==p: return False
  if A.id in NEG: return all_positive(A.a[0],p)
  if A.id in PP0:
    return all_negative(A.a[0],p) and all_negative(A.a[1],p)
  if A.id in NP0:
    return all_positive(A.a[0],p) and all_negative(A.a[1],p)
  return True  # all other variables or constants

def Var(A,typ=VARFVAR): # return set of all variables that occur in formula or list of formulas A
  V = set([])
  if type(A)==list:
    for B in A: V |= Var(B,typ)
    return V
  if A.id in typ:
    V.add(A.id)
  for B in A.a: V |= Var(B,typ)
  return V

def fm(id, arg): # build formula from identifier and argument formulas
  class s(symbol_base):   # create class for this symbol
    pass
  s.id = id
  s.lbp = symbol_table[id].lbp if id in symbol_table.keys() else 0
  s.a = arg
  for A in arg:
    A.lbp = symbol_table[A.id].lbp if A.id in symbol_table.keys() else 0
  return s()

def copy_expr(A):
  if A.a==[]: return A
  else: return fm(A.id,[copy_expr(x) for x in A.a])

def find_split(A,P,positive): # P is the parent of A, needed to modify formula later
  #find a neg join or pos meet in A, not in scope of neg -> or pos circ
  #return parent of this subterm
  if A.a==[]: return None
  if A.id==Invol: return find_split(A.a[0], A, not positive)
  if A.id==Join and not positive or A.id==Meet and positive: return (A,P)
  if A.id==Mult:
    if not positive:
      B = find_split(A.a[0], A, positive)
      if B!=None: return B
      return find_split(A.a[1], A, positive)
    else: return None
  if A.id in [Rimp,Le]:
    if positive:
      B = find_split(A.a[0], A, not positive)
      if B!=None: return B
      return find_split(A.a[1], A, positive)
    else: return None

def split(A): # A is a single *inclusion* formula
  C = find_split(A,None,True)
  if C==None: return [A]
  B = copy_expr(A)
  D = find_split(B,None,True)
  if C[0] is C[1].a[0]: C[1].a[0] = C[0].a[0] 
  else: C[1].a[1] = C[0].a[0]
  if D[0] is D[1].a[0]: D[1].a[0] = D[0].a[1] 
  else: D[1].a[1] = D[0].a[1]
  return split(A) + split(B)

def replace(A,p,B): # in formula A replace variable p by formula B
  if A.id==p: return B
  return fm(A.id,[replace(C,p,B) for C in A.a])

def mono_var_elim(A): # Apply monotone variable elimination rule to an inclusion
  # find all variables in A and eliminate the ones that qualify
  if type(A)==list: return [mono_var_elim(B) for B in A]
  elif A.id==Le:
    Vs = Var(A)
    for p in Vs:
      if all_negative(A.a[0],p) and all_positive(A.a[1],p):
        A = replace(A,p,parse("\\bot"))
      elif all_positive(A.a[0],p) and all_negative(A.a[1],p):
        A = replace(A,p,parse("\\top"))
    return A

def equal(A,B): # Check if two formulas are syntactically identical
  if A.id!=B.id: return False
  if A.a==B.a: return True
  if len(A.a)!=len(B.a): return False
  return all(equal(A.a[i],B.a[i]) for i in range(len(A.a)))

def reduceTF(A): # Apply some valid rewrite rules repeatedly for any subformula B
  # B\circ\bot, \bot\circ B ==> \bot
  # \bot\to B, B\to\top ==> \top
  # B\land B, B\lor B ==> B
  if A.a==[]: return (A,False)
  if A.id==Mult and (A.a[0].id==Bot or A.a[1].id==Bot): return (fm(Bot,[]),True)
  if A.id==Mult and A.a[0].id==Iden: return (A.a[1],True)
  if A.id==Rimp and (A.a[0].id==Bot or A.a[1].id==Top): return (fm(Top,[]),True)
  if A.id==Meet and (A.a[0].id==Bot or A.a[1].id==Bot): return (fm(Bot,[]),True)
  if A.id==Meet and A.a[0].id==Top: return (A.a[1],True)
  if A.id==Meet and A.a[1].id==Top: return (A.a[0],True)
  if A.id in (Meet,Join) and equal(A.a[0],A.a[1]): return (A.a[0],True)
  if A.id==Join and (A.a[0].id==Top or A.a[1].id==Top): return (fm(Top,[]),True)  
  if A.id==Join and A.a[0].id==Bot: return (A.a[1],True)
  if A.id==Join and A.a[1].id==Bot: return (A.a[0],True)
  if A.id==Invol and A.a[0].id==Bot: return (fm(Top,[]),True)
  if A.id==Invol and A.a[0].id==Top: return (fm(Bot,[]),True)
  if A.id==Le and A.a[0].id==Bot: return (fm(TRUE,[]),True)
  if A.id==Le and A.a[0].id==Top and (A.a[1].id in CNOM or A.a[1].id==Bot): return (fm(FALSE,[]),True)
  if A.id==Le and A.a[1].id==Top: return (fm(TRUE,[]),True)
  if A.id==Le and A.a[1].id==Bot and A.a[0].id in NOM: return (fm(FALSE,[]),True)
  if A.id==Le and equal(A.a[0],A.a[1]): return (fm(TRUE,[]),True)
  if A.id==And and (A.a[0].id==FALSE or A.a[1].id==FALSE): return (fm(FALSE,[]),True)
  if A.id==And and A.a[0].id==TRUE: return (A.a[1],True)
  if A.id==And and A.a[1].id==TRUE: return (A.a[0],True)
  if A.id in (And,Or) and equal(A.a[0],A.a[1]): return (A.a[0],True)
  if A.id==Or and (A.a[0].id==TRUE or A.a[1].id==TRUE): return (fm(TRUE,[]),True)  
  if A.id==Or and A.a[0].id==FALSE: return (A.a[1],True)
  if A.id==Or and A.a[1].id==FALSE: return (A.a[0],True)
  if A.id==Imp and equal(A.a[0],A.a[1]): return (fm(TRUE,[]),True)
  Bs = [reduceTF(B) for B in A.a]
  Cs = [B[0] for B in Bs]
  if any(B[1] for B in Bs): return reduceTF(fm(A.id,Cs))
  return (fm(A.id,Cs),False)

def reduce(A):
  if type(A)==str: return A
  B = reduceTF(A)
  if B[1]: return reduce(B[0])
  return B[0]

def first_appr(A,nom="i",cnom="m"):
  if A.id==Le:
    return [fm(A.id,[parse("\\mathbf "+nom),A.a[0]]),
            fm(A.id,[A.a[1],parse("\\mathbf "+cnom)]),
            fm(A.id,[parse("\\mathbf "+nom),parse("\\mathbf "+cnom)])]

freshNOM = 0; freshCNOM = 0
def get_NOM():
  global freshNOM
  freshNOM += 1
  nam = "\\mathbf j_"+(str(freshNOM) if freshNOM<10 else "{"+str(freshNOM)+"}")
  NOM.add(nam)
  symbol(nam)
  return parse(nam)

def get_CNOM():
  global freshCNOM
  freshCNOM += 1
  nam = "\\mathbf n_"+(str(freshCNOM) if freshCNOM<10 else "{"+str(freshCNOM)+"}")
  CNOM.add(nam)
  symbol(nam)
  return parse(nam)

def appr_left(A):
  if A.id==Le:
    if A.a[0].id==Rimp and A.a[1].id in CNOM and A.a[0].a[0].id not in NOM:
      j = get_NOM()
      return [fm(A.id,[fm(Rimp,[j,A.a[0].a[1]]),A.a[1]]),fm(A.id,[j,A.a[0].a[0]])]
    if A.a[1].id==Mult and A.a[0].id in NOM and A.a[1].a[0].id not in NOM:
      j = get_NOM()
      return [fm(A.id,[A.a[0],fm(Mult,[j,A.a[1].a[1]])]),fm(A.id,[j,A.a[1].a[0]])]
    if A.a[0].id==Invol and A.a[1].id in CNOM and A.a[0].a[0].id not in NOM:
      j = get_NOM()
      return [fm(A.id,[fm(Invol,[j]),A.a[1]]),fm(A.id,[j,A.a[0].a[0]])]
  return [A]

def appr_right(A):
  if A.id==Le:
    if A.a[0].id==Rimp and A.a[1].id in CNOM and A.a[0].a[1].id not in CNOM:
      n = get_CNOM()
      return [fm(A.id,[fm(Rimp,[A.a[0].a[0],n]),A.a[1]]),fm(A.id,[A.a[0].a[1],n])]
    if A.a[1].id==Mult and A.a[0].id in NOM and A.a[1].a[1].id not in NOM:
      j = get_NOM()
      return [fm(A.id,[A.a[0],fm(Mult,[A.a[1].a[0],j])]),fm(A.id,[j,A.a[1].a[1]])]
    if A.a[1].id==Invol and A.a[0].id in NOM and A.a[1].a[0].id not in CNOM:
      n = get_CNOM()
      return [fm(A.id,[A.a[0],fm(Invol,[n])]),fm(A.id,[A.a[1].a[0],n])]
  return [A]

def appr_all(As): #appr_left and appr_right until stable
  Bs = As[:] # (shallow) copy list
  while True:
    n = len(Bs)
    Cs = []
    for A in Bs: Cs += appr_left(A)
    Bs = []
    for A in Cs: Bs += appr_right(A)
    if n==len(Bs): break
  return Bs

def signedVars(A, pol): #return list of (var,+/-) of inclusion formula A
  if A.a==[] and A.id in VARFVAR: return [(A.id,pol)]
  if A.id in NEG: return signedVars(A.a[0],not pol)
  if A.id in PP0: return signedVars(A.a[0],pol) + signedVars(A.a[1],pol)
  if A.id in NP0: return signedVars(A.a[0],not pol) + signedVars(A.a[1],pol)
  if A.id in PN0: return signedVars(A.a[0],pol) + signedVars(A.a[1],not pol)
  return []

def exposepos(A,p):
  #print("exposepos",A,p)
  if A.a[1].id==p: return A.a[0]
  if A.a[0].id==Invol:  # ~00 <= 1
    return exposepos(fm(Le,[fm(Dualgc,[A.a[1]]),A.a[0].a[0]]),p)
  if A.a[1].id==Join: # 0 <= 10 v 11
    B = exposepos(fm(Le,[fm(Coimp,[A.a[0],A.a[1].a[1]]),A.a[1].a[0]]),p)
    if type(B)!=str: return B
    return exposepos(fm(Le,[fm(Coimp,[A.a[0],A.a[1].a[0]]),A.a[1].a[1]]),p)
  if A.a[1].id==Rimp: # 0 <= 10 -> 11
    return exposepos(fm(Le,[fm(Mult,[A.a[0],A.a[1].a[0]]),A.a[1].a[1]]),p)
  return "+"+p+" is not exposeable"

def exposeneg(A,p):
  #print("exposeneg",A,p)
  if A.a[0].id==p: return A.a[1]
  if A.a[1].id==Invol:  # 0 <= ~10
    return exposeneg(fm(Le,[A.a[1].a[0],fm(Galcon,[A.a[0]])]),p)
  if A.a[0].id==Meet: # 00 ^ 01 <= 1
    B = exposeneg(fm(Le,[A.a[0].a[0],fm(Himp,[A.a[0].a[1],A.a[1]])]),p)
    if type(B)!=str: return B
    return exposeneg(fm(Le,[A.a[0].a[1],fm(Himp,[A.a[0].a[0],A.a[1]])]),p)
  if A.a[0].id==Mult: # 00 o 01 <= 1
    return exposeneg(fm(Le,[A.a[0].a[0],fm(Rimp,[A.a[0].a[1],A.a[1]])]),p)
  if A.a[1].id==Rimp: # 0 <= 10 -> 11
    return exposeneg(fm(Le,[fm(Mult,[A.a[0],A.a[1].a[0]]),A.a[1].a[1]]),p)
  return "-"+p+" is not exposeable"

def expose(A,p,pol): # A is a single inclusion formula
  # return B s.t. B<=p if pol, else p<=B, or "(pol)p not exposable" or bool 
  # bool is returned if (pol)p is not exposable, True if p occurs in B, False otherwise
  V = signedVars(A,True) # list of signed variables occuring in A
  c = V.count((p,pol))
  #print(A,p,pol,c)
  if c>1: return p+" occurs repeatedly with polarity "+str(pol)
  Vs = set(V)
  if c==0:
    if (p,not pol) not in Vs: return False  #no occurance of p in A
    else: return True
  if (p,not pol) in Vs: return p+" occurs + and - in formula!" # Condition 1 fails; not inductive
  # so p occurs once in A with correct polarity; find it and try to expose it
  return exposepos(A,p) if pol else exposeneg(A,p) # look for p, return other side of exposed inclusion, or error string

def Ackermann(As,p,pol): #As is a quasiequation, p a var, pol a polarity (bool)
  # find all inclusions with exposable variable (pol)p, collect displayed term in expo
  # check p has opposite pol in all other inclusions, collect them in nexpo
  # form disjunction if pol, else conjunction, of all displayed terms and replace p in all nexpo
  expo = []
  nexpo = []
  for A in As:
    B = expose(A,p,pol)
    #print(p,pol)
    #show(A);show(B)
    if type(B)==str: return B
    if type(B)==bool: nexpo.append((A,B)) #B True if p occurs in A, False otherwise
    else: expo.append(B)
  if expo==[]: return ("+" if pol else "-")+p+" has no exposable occurence"  # Condition 3 fails
  C = expo[0]
  for D in expo[1:]: C = fm(Join if pol else Meet,[C,D])
  Bs = [replace(x[0],p,C) if x[1] else x[0] for x in nexpo]
  return Bs

def elim(As,vars,ps,info): #As is a quasiequation of inclusions, try eliminating each p in vars
  if vars == set([]): 
    if info: show(ps,info)
    return As
  for p in vars:
    Bs = Ackermann(As,p,True)
    if type(Bs)!=str: return elim(Bs,vars-{p},ps+["+"+p],info)
    #print(Bs)
    if Bs[-1]=="!": return Bs
    Bs = Ackermann(As,p,False)
    if type(Bs)!=str: return elim(Bs,vars-{p},ps+["-"+p],info)
    #print(Bs)
    if Bs[-1]=="!": return Bs
  return "not inductive; no variable order and no polarity choices succeed!"

def simpl_left(As): # As is a quasiequation
  A = As[-1]
  if A.a==[]: return As
  B = A.a[0]
  if B.id in NOM and B.id not in Var(A.a[1],NOM):
    found = -1
    for i in range(len(As)-1):
      if As[i].a!=[]:
        if As[i].a[0].id==B.id and B.id not in Var(As[i].a[1],NOM) and found==-1: found = i
        elif B.id in Var(As[i],NOM): 
          found = -1
          break
    if found==-1: return As
    i = found
    return As[:i]+As[i+1:-1]+[fm(A.id,[As[i].a[1],A.a[1]])]
  return As

def simpl_right(As):
  A = As[-1]
  if A.a==[]: return As
  B = A.a[1]
  if B.id in CNOM and B.id not in Var(A.a[0],CNOM):
    found = -1
    for i in range(len(As)-1):
      if As[i].a!=[]:
        if As[i].a[1].id==B.id and B.id not in Var(As[i].a[0],CNOM) and found==-1: found = i
        elif B.id in Var(As[i],CNOM): 
          found = -1
          break
    if found==-1: return As
    i = found
    return As[:i]+As[i+1:-1]+[fm(A.id,[A.a[0],As[i].a[0]])]
  return As

def signedwrap(subt,t,pol): # decide when to add parentheses
    return signed(subt,pol) if subt.lbp > t.lbp or subt.a==[] else "("+signed(subt,pol)+")"

def signed(A,pol): #LaTeX string of the signed formula
  if A.a==[]: return "\\stackrel"+("+" if pol else "-")+repr(A)
  if A.id in NEG: return "\\stackrel"+("+" if pol else "-")+A.id+signedwrap(A.a[0],A,not pol)
  else: return signedwrap(A.a[0],A,pol!=(A.id in NP0))+"\\stackrel"+("+" if pol else "-")+\
                         A.id+" "+signedwrap(A.a[1],A,pol!=(A.id in PN0))

def spass(A): #output the formula A in SPASS format
  if A.a==[]: return repr(A).replace("_","").replace("{","").replace("}","").upper()
  return A.id.replace("\\l","").replace("\\","")+"("+",".join([spass(B) for B in A.arg])+")"

def varsInNegArrowOrPosCirc(A,pol):
  if A.a==[]: return set([])
  if A.id in NEG: return varsInNegArrowOrPosCirc(A.a[0], not pol)
  if pol and A.id==Mult or not pol and A.id==Rimp: return set(signedVars(A, pol))
  return varsInNegArrowOrPosCirc(A.a[0],pol!=(A.id in NP0))\
       | varsInNegArrowOrPosCirc(A.a[1],pol!=(A.id in PN0))

def nFO(A): #replace nominal with FO variable
  return fm(A.id.replace("\\mathbf j","x").replace("\\mathbf i","x_0"),[])

def cFO(A): #replace conominal with FO variable
  return fm(A.id.replace("\\mathbf n","y").replace("\\mathbf m","y_0"),[])

def cSimp(A): # if A is an implication of two negated formulas, contrapose A
  if A.id==Imp:
    if A.a[0].id==Not:
      if A.a[1].id==Not:   return fm(Imp,[A.a[1].a[0],A.a[0].a[0]])
      if A.a[1].id==RMnle: return fm(Imp,[fm(RMle,[A.a[1].a[0],A.a[1].a[1]]),A.a[0].a[0]])
    if A.a[0].id==RMnle:
      if A.a[1].id==Not:   return fm(Imp,[A.a[1].a[0],fm(RMle,[A.a[0].a[0],A.a[0].a[1]])])
      if A.a[1].id==RMnle: return fm(Imp,[fm(RMle,[A.a[1].a[0],A.a[1].a[1]]),fm(RMle,[A.a[0].a[0],A.a[0].a[1]])])
    #if equal(A.a[0],A.a[1]): return fm(TRUE,[])
  return A

def  tr(A): # A is a pure quasiequation (=list of inequations), translate it to FO formula
  if type(A)==str: return A
  if type(A)==list:
    if len(A)==1: return tr(A[0])
    if len(A)==2: return cSimp(fm(Imp,[tr(A[0]),tr(A[1])]))
    return cSimp(fm(Imp,[tr(tuple(A[0:-1])),tr(A[-1])]))
  if type(A)==tuple: return fm(And,[tr(A[0]),tr(A[1:])]) if len(A)>1 else tr(A[0])
  if A.id in [TRUE,FALSE]: return A
  if A.id==Le:
    if A.a[0].id in NOM:
      if A.a[1].id in NOM:  return fm(RMle,  [nFO(A.a[1]),nFO(A.a[0])])
      if A.a[1].id in CNOM: return fm(RMnle, [nFO(A.a[0]),cFO(A.a[1])])
      if A.a[1].id==Iden:   return fm(RMiden,[nFO(A.a[0])])
      if A.a[1].id==Bot: return fm(FALSE,[])
      if A.a[1].id==Top: return fm(TRUE, []) #x = nFO(A.a[0]); 
      if A.a[1].id==Mult:
        if A.a[1].a[0].id in NOM:
          if A.a[1].a[1].id in NOM:
            return fm(RMrel,[nFO(A.a[1].a[0]),nFO(A.a[1].a[1]),nFO(A.a[0])])
          j = get_NOM(); x = nFO(j)
          return fm(Exists+" "+x.id,[fm(And,[tr(fm(Le,[j,A.a[1].a[1]])),
                                             fm(RMrel,[nFO(A.a[1].a[0]),x,nFO(A.a[0])])])])
        if A.a[1].a[1].id in NOM:
          j = get_NOM(); x = nFO(j)
          return fm(Exists+" "+x.id,[fm(And,[tr(fm(Le,[j,A.a[1].a[0]])),
                                             fm(RMrel,[x,nFO(A.a[1].a[1]),nFO(A.a[0])])])])
        j = get_NOM(); x = nFO(j); k = get_NOM(); y = nFO(k)
        return fm(Exists+" "+x.id,[fm(Exists+" "+y.id,[fm(And,[fm(And,[tr(fm(Le,[j,A.a[1].a[0]])),
                  tr(fm(Le,[k,A.a[1].a[1]]))]),fm(RMrel,[x,y,nFO(A.a[0])])])])])
      if A.a[1].id==Rimp:  # i <= A->B ---> ioA <= B
        return tr(fm(Le,[fm(Mult,[A.a[0],A.a[1].a[0]]),A.a[1].a[1]]))
      if A.a[1].id==Limp:  # i <= A<-B ---> Boi <= A
        return tr(fm(Le,[fm(Mult,[A.a[0],A.a[1].a[0]]),A.a[1].a[1]]))
      if A.a[1].id==Himp:  # i <= A=>B ---> i^A <= B
        return  tr(fm(Le,[fm(Meet,[A.a[0],A.a[1].a[0]]),A.a[1].a[1]]))
      if A.a[1].id==Coimp: # i <= A-<B ---> all y_n(A-<B <= n ==> i <= n)
        n = get_CNOM()
        return fm(All+" "+cFO(n).id,[cSimp(fm(Imp,[ tr(fm(Le,[A.a[1],n])),tr(fm(Le,[A.a[0],n]))]))])
      if A.a[1].id==Meet:  # i <= A^B ---> i <= A and i <= B
        return fm(And,[tr(fm(Le,[A.a[0],A.a[1].a[0]])),tr(fm(Le,[A.a[0],A.a[1].a[1]]))])
      if A.a[1].id==Join:  # i <= AvB ---> i <= A or i <= B
        return fm(Or,[tr(fm(Le,[A.a[0],A.a[1].a[0]])),tr(fm(Le,[A.a[0],A.a[1].a[1]]))])
      if A.a[1].id==Galcon:  # i <= ~^#A
        return tr(fm(Le,[A.a[1].a[0],fm(Invol,[A.a[0]])]))
      if A.a[1].id==Invol:  # i <= ~A
        if A.a[1].a[0].id in CNOM: # i <= ~m
          return fm(RMle,[fm(RMinvol,[nFO(A.a[0])]),cFO(A.a[1].a[0])])
        if A.a[1].a[0].id in NOM: # i <= ~j
          return fm(RMnle,[nFO(A.a[1].a[0]),fm(RMinvol,[nFO(A.a[0])])])
        j = get_NOM(); x = nFO(j)
        return fm(All+" "+x.id,[cSimp(fm(Imp,[tr(fm(Le,[j,A.a[1].a[0]])),
                                              fm(RMnle,[x,fm(RMinvol,[nFO(A.a[0])])])]))])
      print("missing j <= A case")
      return A
    if A.a[1].id in CNOM:
      if A.a[0].id in CNOM: return fm(RMle,[cFO(A.a[1]),cFO(A.a[0])])
      if A.a[0].id==Iden:   return fm(Not, [fm(RMiden,[cFO(A.a[1])])])
      if A.a[0].id==Bot: return fm(TRUE, [])
      if A.a[0].id==Top: return fm(FALSE,[])
      if A.a[0].id==Mult:
        if A.a[0].a[0].id in NOM:
          if A.a[0].a[1].id in NOM:
            return fm(Not,[fm(RMrel,[nFO(A.a[0].a[0]),nFO(A.a[0].a[1]),cFO(A.a[1])])])
          j = get_NOM(); x = nFO(j)
          return fm(All+" "+x.id,[cSimp(fm(Imp,[tr(fm(Le,[j,A.a[0].a[1]])),
                                    fm(Not,[fm(RMrel,[nFO(A.a[0].a[0]),x,cFO(A.a[1])])])]))])
        if A.a[0].a[1].id in NOM:
          j = get_NOM(); x = nFO(j)
          return fm(All+" "+x.id,[cSimp(fm(Imp,[tr(fm(Le,[j,A.a[0].a[0]])),
                                    fm(Not,[fm(RMrel,[x,nFO(A.a[0].a[1]),cFO(A.a[1])])])]))])
        j = get_NOM(); x = nFO(j)
        k = get_NOM(); y = nFO(k)
        return fm(All+" "+x.id,[fm(All+" "+y.id,[fm(Imp,[ #MISSING CSIMP?
                    fm(And,[tr(fm(Le,[j,A.a[0].a[0]])), tr(fm(Le,[k,A.a[0].a[1]]))]),
                    fm(Not,[fm(RMrel,[x,y,cFO(A.a[1])])])])])])
      if A.a[0].id==Himp: # A=>B <= n ---> all x_j(j <= A=>B ==> j <= n)
        j = get_NOM(); x = nFO(j)
        return fm(All+" "+x.id,[cSimp(fm(Imp,[tr(fm(Le,[j,A.a[0]])), tr(fm(Le,[j,A.a[1]]))]))])
      if A.a[0].id==Coimp: # A-<B <= n ---> A <= B v n
        return tr(fm(Le,[fm(Join,[A.a[0].a[0],A.a[0].a[1]]),A.a[1]]))
      if A.a[0].id==Dualgc:  # i <= ~^#A
        return tr(fm(Le,[fm(Invol,[A.a[1]]),A.a[0].a[0],]))
      if A.a[0].id==Invol:  # ~A <= n
        if A.a[0].a[0].id in CNOM: # ~m <= n
          return fm(RMnle,[fm(RMinvol,[cFO(A.a[1])]),cFO(A.a[0].a[0])])
        if A.a[0].a[0].id in NOM: # ~j <= n
          return fm(RMle,[nFO(A.a[0].a[0]),fm(RMinvol,[cFO(A.a[1])])])
        j = get_NOM(); x = nFO(j)
        return fm(Exists+" "+x.id,[fm(And,[tr(fm(Le,[j,A.a[0].a[0]])),
                                           fm(RMle,[x,fm(RMinvol,[cFO(A.a[1])])])])])
      if A.a[0].id==Rimp:
        if A.a[0].a[0].id in NOM:
          if A.a[0].a[1].id in CNOM:
            return fm(RMrel,[cFO(A.a[1]),nFO(A.a[0].a[0]),cFO(A.a[0].a[1])])
      if A.a[0].id==Meet:  # A^B <= m ---> A <= m or B <= m
        return fm(Or,[tr(fm(Le,[A.a[0].a[0],A.a[1]])),tr(fm(Le,[A.a[0].a[1],A.a[1]]))])
      if A.a[0].id==Join:  # AvB <= m ---> A <= m and B <= m
        return fm(And,[tr(fm(Le,[A.a[0].a[0],A.a[1]])),tr(fm(Le,[A.a[0].a[1],A.a[1]]))])
      print("missing A <= m case")
      return A
    j = get_NOM()
    return fm(All+" "+nFO(j).id,[cSimp(fm(Imp,[tr(fm(Le,[j,A.a[0]])),tr(fm(Le,[j,A.a[1]]))]))])
  print("missing a case: "+A.id)
  return A

### User commands ##############################################

def signedformula(st,sign=True): # input (raw) LaTeX formula, output LaTeX signed LaTeX string
  return signed(parse(st),sign)

def Sahlqvist(st): #check if LaTeX string is a Sahlqvist formula
  # i.e. for all p, all occur. of +p OR all occur. of -p do not occur in scope of -\to or +o 
  V = sorted(v[0] for v in varsInNegArrowOrPosCirc(parse(st),True))
  for i in range(len(V)-1):
    if V[i]==V[i+1]: return V[i]+" occurrs + and - in scope of -\\to or +\\circ"
  return True

def preprocess(st,info=True): # st is a single formula (LaTeX string), output is a list of inclusion formulas
  A = parse(st)
  if info: 
    display(Math("\\ "))
    show(A,info)
  if A.id==Rimp:
    A = fm(Le,[A.a[0],A.a[1]])
  elif A.id!=Le:
    A = fm(Le,[parse("\\mathbf t"),A])
  As = mono_var_elim(split(A))
  if info: show(As,info)
  return As

def approximate(As,info=True): # apply approximation rules exhaustively (starting with first approximation)
  global freshNOM, freshCNOM
  Cs = []
  for B in As:
    if len(Var(B))==0: Bs = [B]
    else:
      Bs = first_appr(B)
      Bs = [y for x in Bs for y in split(x)]
      if info: showq(Bs,info)
      C = Bs[-1] #store conclusion
      Bs = Bs[:-1]
      freshCNOM = 0
      freshNOM = 0
      fixed = [] #can't be approx or split
      while Bs!=[]:
        Ds = appr_all(Bs)
        if len(Ds)!=len(Bs):
          Bs = []
          for A in Ds:
            spl = split(A)
            if len(spl)==1: fixed += spl
            else: 
              Bs += spl
              #print(spl)
        else:
          Bs = []
          fixed += Ds
      Bs = fixed+[C]
    if info: showq(Bs,info)
    Cs.append(Bs)
  return Cs

def eliminate(As, info=True):
  Ds = []
  for Bs in As:
    V = set(p for B in Bs for p in Var(B))
    Cs = elim(Bs, V, [], info)
    if info: 
      if info==True and type(Cs)==str: print(Cs)
      else: showq(Cs,info)
    Ds.append(Cs)
  return Ds

def simplify(As, info=True):
  Ds = []
  for Bs in As:
    if type(Bs)==str:
      return Bs
    Cs = [reduce(B) for B in Bs]
    Cs = [B for B in Cs[:-1] if B.id!=TRUE]+[Cs[-1]]
    #if any(B.id==FALSE for B in Cs[:-1]) or Cs[-1].id==TRUE: 
    #  Cs = [fm(Le,[fm("\\mathbf i",[]),fm("\\mathbf i",[])])]
    Cs = simpl_left(Cs)
    Cs = simpl_right(Cs)
    Cs = [reduce(B) for B in Cs]
    Cs = [B for B in Cs[:-1] if B.id!=TRUE]+[Cs[-1]]
    #if any(B.id==FALSE for B in Cs[:-1]) or Cs[-1].id==TRUE: 
    #  Cs = [fm(Le,[fm("\\mathbf i",[]),fm("\\mathbf i",[])])]
    showq(Cs,info)
    Ds.append(Cs)
  return Ds

def translate(A): # input a list of quasiequations
  if type(A)==str: return A
  if type(A)==list and type(A[0])==list:
    return fm(And,[tr(A[0]),translate(A[1:])]) if len(A)>1 else tr(A[0])
  return tr(A)

def purify(st, info=True):
  # purify(r"LaTeX formula")  prints intermediate steps (typeset) and returns the purified form of the 
  #   LaTeX formula or a string "explaining" why no purified formula exists
  #
  # purify(r"LaTeX formula",False) returns *only* the purified form of the LaTeX formula or a string 
  #   with information why no purified formula exists
  #
  # purify(r"LaTeX formula","steps") returns a list of all steps as LaTeX strings (with Python \\ format)
  #
  # purify(r"LaTeX formula","latex") *prints* a list of all steps as LaTeX strings (with single \ format)
  #   useful for copy/paste into a LaTeX document
  global output_list
  output_list=[]
  As = simplify(eliminate(approximate(preprocess(st,info),info),info),info)
  if info=="steps": return output_list
  if info=="latex":
    for st in output_list: print(st)
  else: return As

def pearl(st, info=True): #this is the full algorithm, with output options similar to purify
  global output_list
  output_list=[]
  As = reduce(translate(simplify(eliminate(approximate(preprocess(st,info),info),info),info)))
  if info==True and type(As)!=str: show(As)
  if info=="steps": return output_list+[str(As)]
  if info=="latex":
    for st in output_list: print(st)
    print(As)
  else: return As
