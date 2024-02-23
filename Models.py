# Python code for finite first order models

def opstr(m):  # convert 2-dim list to a compact string for display
    nr = len(m)
    if nr == 0:
        return "[]"
    nc = len(m[0])
    s = [[str(y).replace(' ', '') for y in x] for x in m]
    width = [max([len(s[x][y]) for x in range(nr)]) for y in range(nc)]
    s = [[" "*(width[y]-len(s[x][y]))+s[x][y] for y in range(nc)]
         for x in range(nr)]
    rows = ["["+",".join(x)+"]" for x in s]
    s = "[\n"+",\n".join(rows)+"]"
    return s


def oprelstr(oprel):  # convert a list of operations or relations to a string
    st = ''
    for x in oprel:
        if type(oprel[x]) == list and type(oprel[x][0]) == list:
            st += '\n"'+x+'":' + opstr(oprel[x]) + ', '
        else:
            st += '"'+x+'":' + str(oprel[x]) + ', '
    return st[:-2]


def op_var_pos_diag(op, s, c):
    if type(op[s]) == list:
        base = range(len(op[s]))
        if type(op[s][0]) == list:
            return [c+str(x)+" "+s+" "+c+str(y)+" = "+c+str(op[s][x][y])
                    for x in base for y in base]
        elif s == "'":
            return [c+str(x)+s+" = "+c+str(op[s][x]) for x in base]
        else:
            return [s+"("+c+str(x)+") = "+c+str(op[s][x]) for x in base]
    else:
        return [s+" = "+c+str(op[s])]


def rel_var_pos_diag(rel, s, c):
    if type(rel[s]) == list:
        base = range(len(rel[s]))
        if type(rel[s][0]) == list:
            if type(rel[s][0][0]) == list:  # if prefix ternary relation
                return [s+"("+c+str(x)+","+c+str(y)+","+c+str(z)+")"
                        for x in base for y in base for z in base if rel[s][x][y][z]]
            else:  # if infix binary relation
                return [c+str(x)+" "+s+" "+c+str(y)
                        for x in base for y in base if rel[s][x][y]]
        else:
            return [s+"("+c+str(x)+")" for x in base if rel[s][x]]
    else:
        return "not a relation"


def op_var_diag(op, s, c, n=0):
    if type(op[s]) == list:
        base = range(len(op[s]))
        if type(op[s][0]) == list:
            return [c+str(x+n)+" "+s+" "+c+str(y+n)+" = "+c+str(op[s][x][y]+n)
                    for x in base for y in base]
        elif s == "'":
            return [c+str(x+n)+s+" = "+c+str(op[s][x]+n) for x in base]
        else:
            return [s+"("+c+str(x+n)+") = "+c+str(op[s][x]+n) for x in base]
    else:
        return [s+" = "+c+str(op[s]+n)]


def rel_var_diag(rel, s, c, n=0):
    if type(rel[s]) == list:
        base = range(len(rel[s]))
        if type(rel[s][0]) == list:
            if type(rel[s][0][0]) == list:  # prefix ternary relation
                return [("" if rel[s][x][y][z] else "-")+s+"("+c+str(x+n) +
                        ","+c+str(y+n)+","+c+str(z+n)+")"
                        for x in base for y in base for z in base]
            elif s >= "A" and s <= "Z":  # prefix binary relation
                return [("" if rel[s][x][y] else "-")+s+"("+c+str(x+n) +
                        ","+c+str(y+n)+")" for x in base for y in base]
            else:  # infix binary relation
                return [("(" if rel[s][x][y] else "-(")+c+str(x+n)+" " +
                        s+" "+c+str(y+n)+")" for x in base for y in base]
        else:
            return [("" if rel[s][x] else "-")+s+"("+c+str(x+n)+")"
                    for x in base]
    else:
        return "not a relation"


def op_hom(A, B):  # return string of homomorphism equations
    st = ''
    for s in B.operations:
        if type(B.operations[s]) == list:
            if type(B.operations[s][0]) == list:
                st += " & h(x "+s+" y) = h(x) "+s+" h(y)"
            elif s == "'":
                st += " & h(x') = h(x)'"
            else:
                st += " & h("+s+"(x)) = "+s+"(h(x))"
        else:
            st += " & h("+str(B.operations[s] +
                              A.cardinality)+") = "+str(A.operations[s])
    return st


def aritystr(t): return ("(_,_)" if type(
    t[0]) == list else "(_)") if type(t) == list else ""


def op2li(t): return ([x for y in t for x in y] if type(
    t[0]) == list else t) if type(t) == list else [t]


class Model():
    def __init__(self, cardinality, index=None, operations={}, relations={},
                 **kwargs):
        """
        Construct a finite first-order model.

        INPUT:
            cardinality -- number of elements of the model's base set
            index -- a natural number giving the position of the model 
                in a list of models
            operations  -- a dictionary of operations on [0..cardinality-1].
                Entries are symbol:table pairs where symbol is a string 
                that denotes the operation symbol, e.g. '+', and table is
                an n-dimensional array with entries from [0..cardinality-1].
                n >= 0 is the arity of the operation (not explicitly coded 
                but can be computed from the table).
            relations -- a dictionary of relations on [0..cardinality-1].
                Entries are symbol:table pairs where symbol is a string 
                that denotes the relation symbol, e.g. '<', and table is
                an n-dimensional array with entries from [0,1] (coding 
                False/True). Alternatively the table can be an 
                (n-2)-dimensional array with entries that are dictionaries
                with keys [0..cardinality-1] and values subsets of [0..cardinality-1],
                given as ordered lists.
                n >= 0 is the arity of the relation (not explicitly coded 
                but can be computed from the table).
            other optional arguments --
                uc  -- a dictionary with keys [0..cardinality-1] and values 
                    an ordered list of upper covers. Used for posets.
                pos -- list of [x,y] coordinates for element positions
                labels -- list of n strings that give a label for each element
                is_... -- True/False properties are stored here
        """

        self.cardinality = cardinality
        self.index = index
        self.operations = operations
        self.relations = relations
        for attr in kwargs:
            setattr(self, attr, kwargs[attr])

    def __repr__(self):
        """
        display a model
        """
        st = '\nModel(cardinality = '+str(self.cardinality) +\
             (', index = '+str(self.index) if self.index != None else '')
        if self.operations != {}:
            st += ',\noperations = {' + oprelstr(self.operations) + '}'
        if self.relations != {}:
            st += ',\nrelations = {' + oprelstr(self.relations) + '}'
        other = set(vars(self)) - \
            set(["cardinality", "index", "operations", "relations"])
        for attr in other:
            st += ',\n' + attr + ' = ' + str(getattr(self, attr))
        return st + ')'

    def positive_diagram(self, c):
        """
        Return the positive diagram of the algebra or structure
        """
        li = []
        for x in self.operations:
            li += op_var_pos_diag(self.operations, x, c)
        for x in self.relations:
            li += rel_var_pos_diag(self.relations, x, c)
        return li

    def diagram(self, c, s=0):
        """
        Return the diagram of the algebra or structure, prefix c, shift s
        """
        li = []
        for x in range(self.cardinality):
            for y in range(x+1, self.cardinality):
                li += ["-("+c+str(x+s)+"="+c+str(y+s)+")"]
        for x in self.operations:
            li += op_var_diag(self.operations, x, c, s)
        for x in self.relations:
            li += rel_var_diag(self.relations, x, c, s)
        return li

    def find_extensions(self, cls, cardinality, mace_time=60):
        """
        Find extensions of this model of given cardinality card in FOclass cls
        """
        n = self.cardinality
        ne = ['c'+str(x)+'!=c'+str(y) for x in range(n) for y in range(x+1, n)]
        return prover9(cls.axioms+ne+self.positive_diagram('c'), [],
                       mace_time, 0, cardinality)

    def inS(self, B, info=False):
        """
        check if self is a subalgebra of B, if so return sublist of B
        """
        if self.cardinality > B.cardinality:
            return False
        if info:
            print(self.diagram('a')+B.diagram(''))
        m = prover9(self.diagram('a')+B.diagram(''), [],
                    6000, 0, B.cardinality, [], True)
        if len(m) == 0:
            return False
        return [m[0].operations['a'+str(i)] for i in range(self.cardinality)]

    def inH(self, B, info=False):
        """
        check if self is a homomorphic image of B, if so return homomorphism
        """
        if self.cardinality > B.cardinality:
            return False
        formulas = self.diagram('')+B.diagram('', self.cardinality) +\
            ['A('+str(i)+')' for i in range(self.cardinality)] +\
            ['-B('+str(i)+')' for i in range(self.cardinality)] +\
            ['B('+str(i)+')' for i in range(self.cardinality, self.cardinality+B.cardinality)] +\
            ['-A('+str(i)+')' for i in range(self.cardinality, self.cardinality+B.cardinality)] +\
            ['B(x) & B(y) -> A(h(x)) & A(h(y))'+op_hom(self, B),
             'A(y) -> exists x (B(x) & h(x) = y)']
        if info:
            print(formulas)
        m = prover9(formulas, [], 6000, 0,
                    self.cardinality+B.cardinality, [], True)
        if len(m) == 0:
            return False
        return m[0].operations['h'][self.cardinality:]

    def product(self, B, info=False):
        base = [[x,y] for x in range(self.cardinality) for y in range (B.cardinality)]
        if info: print(base)
        op = {}
        for f in B.operations:
            fA = self.operations[f]
            fB = B.operations[f]
            if type(fB)==list:
                if type(fB[0])==list:
                    op[f] = [[base.index([fA[p[0]][q[0]],fB[p[1]][q[1]]])
                               for p in base] for q in base]
                else:
                    op[f] = [base.index([fA[p[0]],fB[p[1]]]) for p in base]
            else:
                op[f] = base.index([fA,fB])
        rel = {}
        for r in B.relations:
            rA = self.relations[r]
            rB = B.relations[r]
            if type(rB[0])==list:
                rel[r] = [[1 if rA[p[0]][q[0]]==1 and rB[p[1]][q[1]]==1 else 0
                             for p in base] for q in base]
            else:
                rel[r] =[1 if rA[p[0]]==1 and rB[p[1]]==1 else 0 for p in base]
        return Model(len(base),None,op,rel)

    def uacalc_format(self, name):
        """
        display a model in UAcalc format (uacalc.org)
        """
        st = '<?xml version="1.0"?>\n<algebra>\n  <basicAlgebra>\n    <algName>'+\
             name+(str(self.index) if self.index!=None else '')+\
             '</algName>\n    <cardinality>'+str(self.cardinality)+\
             '</cardinality>\n    <operations>\n'
        for x in self.operations:
            st += '      <op>\n        <opSymbol>\n          <opName>'+\
                  x+'</opName>\n'
            oplst = type(self.operations[x]) == list
            if oplst and type(self.operations[x][0]) == list:
                st += '          <arity>2</arity>\n        </opSymbol>\n        <opTable>\n          <intArray>\n' + xmlopstr(self.operations[x])
            else:
                st += '          <arity>'+('1' if oplst else '0')+'</arity>\n        </opSymbol>\n        <opTable>\n          <intArray>\n            <row>' + (str(self.operations[x])[1:-1] if oplst else str(self.operations[x]))+'</row>\n'
            st += '          </intArray>\n        </opTable>\n      </op>\n'
        return st+'    </operations>\n  </basicAlgebra>\n</algebra>\n'

    @staticmethod
    def mace4format(A):
        if A.is_lattice():
            A.get_join()
        st = "interpretation("+str(A.cardinality) + \
            ", [number = "+str(A.index)+", seconds = 0], [\n"
        st += ',\n'.join([" function("+s+aritystr(A.operations[s])+", " +
                          str(op2li(A.operations[s])).replace(" ", "")+")" for s in A.operations])
        if len(A.operations) > 0 and len(A.relations) > 0:
            st += ',\n'
        st += ',\n'.join([" relation("+s+aritystr(A.relations[s])+", " +
                          str(op2li(A.relations[s])).replace(" ", "")+")" for s in A.relations])
        return st+"])."

import networkx as nx
from graphviz import Graph
from IPython.display import display_html
def hasse_diagram(op,rel,dual,unary=[]):
    A = range(len(op))
    G = nx.DiGraph()
    if rel:
        G.add_edges_from([(x,y) for x in A for y in A if (op[y][x] if dual else op[x][y]) and x!=y])
    else: 
        G.add_edges_from([(x,y) for x in A for y in A if op[x][y]==(y if dual else x) and x!=y])
    try:
        G = nx.algorithms.dag.transitive_reduction(G)
    except:
        pass
    P = Graph()
    P.attr('node', shape='circle', width='.15', height='.15', fixedsize='true', fontsize='10')
    for x in A: P.node(str(x), color='red' if unary[x] else 'black')
    P.edges([(str(x[0]),str(x[1])) for x in G.edges])
    return P

def show(li,symbols="<= +", unaryRel=""):
    if type(li)!=list: li = [li]
    # use graphviz to display a mace4 structure as a diagram
    # symbols is a list of binary symbols that define a poset or graph
    # unaryRel is a unary relation symbol that is displayed by red nodes
    i = 0
    sy = symbols.split(" ")
    #print(sy)
    st = ""
    for x in li:
        st+=str(i)
        i+=1
        uR = x.relations[unaryRel] if unaryRel!="" else [0]*x.cardinality
        for s in sy:
            t = s[:-1] if s[-1]=='d' else s
            if t in x.operations.keys():
                st+=hasse_diagram(x.operations[t],False,s[-1]=='d',uR)._repr_image_svg_xml()+"&nbsp; &nbsp; &nbsp; "
            elif t in x.relations.keys():
                st+=hasse_diagram(x.relations[t], True, s[-1]=='d',uR)._repr_image_svg_xml()+"&nbsp; &nbsp; &nbsp; "
        st+=" &nbsp; "
    display_html(st,raw=True)
