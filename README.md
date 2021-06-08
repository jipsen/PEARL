# PEARL
Correspondence theory for relevance logics


Notes:
1. The implementation language is Python
1. Formulas are entered as latex strings, output is produced as latex strings.
1. Output uses the same syntax rules as input.
1. A subset of standard latex is used; fixed macro names can also be defined (see Macros string).
1. Only parentheses (...) are used as delimiters.
1. The signature is specified by commands for each symbol followed by a binding strength.
1. Unary symbols can be written prefix or postfix without delimiters.
1. Binary symbols are written infix.
1. Quantifiers must be followed by a single variable.
1. Quantifiers can be followed by a space or no space.
1. The scope of quantifiers is either atomic (nonatomic formulas must be delimited) or nonatomic.
1. White space is optional.
1. Some variables can be followed by (single digit) subscripts (see header code).
1. PEARL stands for Propositional Elimination Algorithm for Relevance Logic. It is an implementation of distributive ALBA for the signature of relevance algebras and logics.

Specifically, for relevance logic and PEARL the extended propositional syntax is

* Formula variables: "A", "B", "C", "D", "E", "\alpha", ...
* Variables (VAR): "p", "q", "r", "p_1", "p_2", ...
* Nominals (NOM): "\mathbf i", "\mathbf j", "\mathbf j_1", ...
* Co-nominals (CNOM): "\mathbf m", "\mathbf n", "\mathbf n_1", ...
* Truth constant: "\mathbf t"
* Bounds: "\top", "\bot"
* Conjunction: "\land"
* Disjunction: "\lor"
* Negation: "\sim" or "{\sim}" (better for typesetting)
* Fusion: "\circ"
* Relevant implication: "\to"
* Heyting implication: "\Rightarrow"
* Co-Heyting implication: "\coimp" (uses an example macro)
* Formula inclusion: "\le"
* Quasi-inclusion implication: "\implies"

The first-order language for Routley-Meyer frames (for output only) is

* Unary rel (prefix): "Ox"
* Ternary rel (prefix): "Rxyz"
* Binary rel (infix): "\preceq"
* Unary op (postfix): "^\sim"

See the header code for full details. Symbols can be adjusted (with some care).

The internal representation of a formula is an abstract syntax tree in the form of a nested Python dictionary. 

E. g., "p\circ \mathbf t" translates to 
```
{"id":"\circ",
 "bp":7,
 "a":[{"id":"p", 
       "bp":0,
       "a":[]},
      {"id":"\mathbf t", 
       "bp":0,
       "a":[]}]
}
```

"id" stands for "identifier" (a symbol string).

"bp" stands for binding power, used when converting a formula to a string

"a" is a list of argument formulas

More information about each symbol (type, ...) is determined from named lists (see header code).

The PEARL algorithm operates on the abstract syntax tree.

Most steps of PEARL are implemented by (short) recursive functions that traverse the syntax tree.
