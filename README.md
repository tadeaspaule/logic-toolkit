# logic-toolkit
All functionality is held in a LogicToolkit class.<br>
You can either import the class, or simply run the script in the terminal, it has a command-parsing component<br>

Holds the following functionality for working with logic formulas:<br><i>
    - Convert formula to CNF or DNF form<br>
    - Check if a formula is a tautology / contradiction / satisfiable<br>
    - Get True interpretations<br>
    - Get definite rules from a given formula<br>
    - Manually add definite rules<br>
    - Make queries<br>
    - Generate random logical formulas<br></i>
<br>
The following notation is expected when inputting logical formulas:<br><i>
    - Single, uppercase letters for literals (A,B,...)<br>
    - 'a'  = conjunction, for example AaB<br>
    - 'v'  = disjunction, for example AvC, Av(BaC)<br>
    - '->' = implication, for example A->B, A->(BvC)<br>
    - '!'  = negation, for example !A, A->!(BvC)<br></i>
