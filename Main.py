# FSA
# If error appears it exits the program
class Graph:
    edges = {}
    states = {}
    arr = []

    # Adding state to the graph
    def addNode(self, node):
        a = Node(node)
        self.states[node] = a
        self.arr.append(a)

    # Adding alpha to the graph
    def addEdge(self, edge):
        self.edges[edge] = Edge(edge)

    def __init__(self):
        self.edges = {}
        self.states = {}
        self.initState = None
        self.finalStates = list()
        self.disjoint = False
        self.complete = False
        self.acceptingExist = True
        self.reachable = True
        self.determ = True

    def findNode(self, state):
        if state in self.states:
            return self.states[state]
        return -1

    def findEdge(self, alpha):
        if alpha in self.edges:
            return self.edges[alpha]
        return -1

    def acceptingState(self):
        if self.finalStates == []:
            self.acceptingExist = False

    # Checking for disjoining error and reachable warning
    def disjointTest(self):
        q = list()
        q.append(self.initState)
        while len(q) != 0:
            curent = q.pop()
            curent.visited = True
            for i in curent.outputEdges:
                for j in i.data:
                    if curent == j[0] and not j[1].visited:
                        q.append(j[1])

        for i in self.states:
            if not self.states[i].visited:
                output = open("result.txt", "w")
                output.write("Error:\nE2: Some states are disjoint")
                exit(0)

    # Checking for deterministic FSA
    def deterministic(self):
        for i in self.states:
            k = set()
            for j in self.states[i].outputEdges:
                if j in k:
                    output = open("result.txt", "w")
                    output.write("Error:\nE6: FSA is nondeterministic")
                    exit(0)
                k.add(j)

    def getRegExp(self):
        result = ""

        if not self.finalStates:
            return "{}"

        for i in self.finalStates:
            result += self.getReg(self.initState, i, len(self.arr) - 1) + "|"

        if result == "":
            return "{}"
        else:
            return result[:-1]

    def getReg(self, i, j, k):
        expr = ""
        if k == -1:
            for output in i.outputEdges:
                for outputState in output.data:
                    if outputState[0] == i and outputState[1] == j:
                        expr += output.alpha + "|"
                        break
            if i == j:
                expr += "eps"
            if len(expr) == 0:
                expr = "{}"
            if expr.endswith("|"):
                expr = expr[:-1]
            return "(" + expr + ")"

        if k == len(self.arr) - 1:
            return (self.getReg(i, self.arr[k], k - 1) + self.getReg(self.arr[k], self.arr[k], k - 1) + "*" + self.getReg(self.arr[k], j, k - 1) + "|" + self.getReg(i, j, k - 1))
        else:
            return ("(" + self.getReg(i, self.arr[k], k - 1) + self.getReg(self.arr[k], self.arr[k], k - 1) + "*" + self.getReg(self.arr[k], j, k - 1) + "|" + self.getReg(i, j, k - 1) + ")")


# Class that contains states and has links to the alphas
class Node:
    def __init__(self, state):
        self.state = state
        self.visited = False
        self.inputEdges = list()
        self.outputEdges = list()


# Class that contains alphas and has links to the states
class Edge:
    def __init__(self, alpha):
        self.alpha = alpha
        self.visited = False
        self.data = list()


# Preparing input and catching malformed, initial state errors
def refactoringInput():
    output = open("result.txt", "w")
    inputFile = open("fsa.txt", "r")
    inputLine = inputFile.readline().strip().replace(" ", "")
    if inputLine.startswith("states={"):
        inputLine = inputLine.replace("states={", "")
        inputLine = inputLine.replace("}", "")
        arrayOfStates = inputLine.split(",")
    else:
        output.write("Error:\nE5: Input file is malformed")
        exit(0)

    inputLine = inputFile.readline().strip().replace(" ", "")
    if inputLine.startswith("alpha={"):
        inputLine = inputLine.replace("alpha={", "")
        inputLine = inputLine.replace("}", "")
        arrayOfEdges = inputLine.split(",")
    else:
        output.write("Error:\nE5: Input file is malformed")
        exit(0)

    inputLine = inputFile.readline().strip().replace(" ", "")
    if inputLine.startswith("init.st={"):
        inputLine = inputLine.replace("init.st={", "")
        inputLine = inputLine.replace("}", "")
        initState = inputLine
        if initState == "":
            output.write("Error:\nE4: Initial state is not defined")
            exit(0)
    else:
        output.write("Error:\nE5: Input file is malformed")
        exit(0)

    inputLine = inputFile.readline().strip().replace(" ", "")
    if inputLine.startswith("fin.st={"):
        inputLine = inputLine.replace("fin.st={", "")
        inputLine = inputLine.replace("}", "")
        arrayOfFinalStates = inputLine.split(",")
    else:
        output.write("Error:\nE5: Input file is malformed")
        exit(0)

    inputLine = inputFile.readline().strip().replace(" ", "")
    if inputLine.startswith("trans={"):
        inputLine = inputLine.replace("trans={", "")
        inputLine = inputLine
        inputLine = inputLine.replace("}", "")
        arrayOfTransactions = inputLine.split(",")
    else:
        output.write("Error:\nE5: Input file is malformed")
        exit(0)

    return [arrayOfStates, arrayOfEdges, initState, arrayOfFinalStates, arrayOfTransactions]


# Filling the graph and catching not represented states and transitions errors
def fillingTheGraph():
    fsa = Graph()
    output = open("result.txt", "w")
    refactoredString = refactoringInput()
    for i in refactoredString[0]:
        fsa.addNode(i)
    for i in refactoredString[1]:
        fsa.addEdge(i)

    if fsa.findNode(refactoredString[2]) != -1:
        fsa.initState = fsa.findNode(refactoredString[2])
    else:
        output.write("Error:\nE1: A state '" + refactoredString[2] + "' is not in set of states")
        exit(0)

    if refactoredString[3] != [""]:
        for i in refactoredString[3]:
            if fsa.findNode(i) != -1:
                fsa.finalStates.append(fsa.findNode(i))
            else:
                output.write("Error:\nE1: A state '" + i + "' is not in set of states")
                exit(0)

    for i in refactoredString[4]:
        elem = i.split(">")
        if (fsa.findNode(elem[0]) != -1) & (fsa.findNode(elem[2]) != -1):
            if fsa.findEdge(elem[1]) != -1:
                firstState = fsa.findNode(elem[0])
                secondState = fsa.findNode(elem[2])
                transition = fsa.findEdge(elem[1])
                transition.data.append([firstState, secondState])
                firstState.outputEdges.append(transition)
                secondState.inputEdges.append(transition)
            else:
                output.write("Error:\nE3: A transition '" + elem[1] + "' is not represented in the alphabet")
                exit(0)
        else:
            if fsa.findNode(elem[0]) == -1:
                output.write("Error:\nE1: A state '" + elem[0] + "' is not in set of states")
            else:
                output.write("Error:\nE1: A state '" + elem[2] + "' is not in set of states")
            exit(0)

    return fsa


fsa = fillingTheGraph()
fsa.acceptingState()
fsa.disjointTest()
fsa.deterministic()

# Writing output
output = open("result.txt", "w")
output.write(fsa.getRegExp())
output.close
